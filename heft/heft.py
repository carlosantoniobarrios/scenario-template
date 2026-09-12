#!/usr/bin/env python3

import json
import re
import math
import os
import glob
import csv
import argparse
import fnmatch
import time
import concurrent.futures
import multiprocessing

class EdgeScheduler:
    def __init__(self, json_data):
        self.nodes = []
        self.links = {}
        self.dag = {}
        self.tasks = []
        
        self.delay_matrix = {}
        self.comp_matrix = {} # comp_matrix[task][node] = time_in_ns
        
        # Cap on the number of re-ranking passes used by schedule_heft_cabeee_mod2()
        self.max_heft_iterations = 100

        # Budget for schedule_exhaustive(): maximum number of candidate task
        # placements the search may evaluate before it gives up on proving optimality.
        self.max_exhaustive_evaluations = 10_000_000

        # A-Beam beam width k: how many branches survive the prune at each DAG step.
        # An int is a constant width; a callable k(step_index, total_steps) -> int lets
        # the width vary with depth (e.g. wider early, narrower near the end).
        self.abeam_beam_width = 10

        # A step's hosting combinations are enumerated exactly while their product stays
        # at or below this; above it the step is expanded service by service with the
        # beam applied inside the step too. See schedule_abeam().
        self.abeam_max_step_combinations = 20_000

        self._parse_json(json_data)
        self._compute_all_pairs_shortest_path()
        
    def _parse_time_to_ns(self, time_str):
        """Converts strings like '1ms', '100us' into nanoseconds."""
        match = re.match(r"([\d\.]+)([a-zA-Z]+)", time_str)
        if not match: return 0
        val = float(match.group(1))
        unit = match.group(2).lower()
        if unit == "ms": return int(val * 1_000_000)
        elif unit == "us": return int(val * 1_000)
        elif unit == "ns": return int(val)
        elif unit == "s": return int(val * 1_000_000_000)
        return int(val)

    def _parse_json(self, data):
        # Parse Routers (Nodes)
        self.nodes = [r['node'] for r in data.get('router', [])]
        
        # Parse Links and Delays
        for link in data.get('link', []):
            u, v = link['from'], link['to']
            delay_ns = self._parse_time_to_ns(link['delay'])
            if u not in self.links: self.links[u] = {}
            if v not in self.links: self.links[v] = {}
            self.links[u][v] = delay_ns
            self.links[v][u] = delay_ns # Assuming bidirectional
            
        # Parse DAG
        dag_data = data.get('dag', {}).get('dag1', {})
        self.tasks = list(dag_data.keys())
        
        # Add tasks that are targets but not sources in the dict
        for targets in dag_data.values():
            for t in targets.keys():
                if t not in self.tasks:
                    self.tasks.append(t)
                    
        self.dag = {t: [] for t in self.tasks}
        self.dag_parents = {t: [] for t in self.tasks}
        
        for parent, children in dag_data.items():
            for child in children.keys():
                self.dag[parent].append(child)
                self.dag_parents[child].append(parent)

        # Parse Router Hosting (Computation Matrix)
        self.comp_matrix = {t: {} for t in self.tasks}
        for rh in data.get('routerHosting', []):
            svc = rh['service']
            rtr = rh['router']

            # Use makespanNS if available, otherwise default to 0
            cost = rh.get('makespanNS', 0)

            if svc in self.comp_matrix:
                self.comp_matrix[svc][rtr] = cost

        # Fallback for instance-suffixed hosting names. The DAG names the consumer
        # sink task "/consumer", but routerHosting pins it under its instance name
        # ("/consumer1", "/consumer2", ...). Match any still-unhosted task against a
        # routerHosting service that is the task name followed only by digits, so
        # "/consumer" picks up "/consumer1" and lands on its pinned router.
        for task, hosts in self.comp_matrix.items():
            if hosts:
                continue
            for rh in data.get('routerHosting', []):
                svc = rh['service']
                if re.fullmatch(re.escape(task) + r"\d+", svc):
                    self.comp_matrix[task][rh['router']] = rh.get('makespanNS', 0)

    def _compute_all_pairs_shortest_path(self):
        """Floyd-Warshall to get shortest path delay between all routers."""
        self.delay_matrix = {u: {v: math.inf for v in self.nodes} for u in self.nodes}
        for u in self.nodes:
            self.delay_matrix[u][u] = 0
            if u in self.links:
                for v, delay in self.links[u].items():
                    self.delay_matrix[u][v] = delay
                    
        for k in self.nodes:
            for i in self.nodes:
                for j in self.nodes:
                    if self.delay_matrix[i][j] > self.delay_matrix[i][k] + self.delay_matrix[k][j]:
                        self.delay_matrix[i][j] = self.delay_matrix[i][k] + self.delay_matrix[k][j]

        # Compute average communication cost for rank calculations
        total_delay, count = 0, 0
        for i in self.nodes:
            for j in self.nodes:
                if i != j and self.delay_matrix[i][j] != math.inf:
                    total_delay += self.delay_matrix[i][j]
                    count += 1
        self.avg_comm = total_delay / count if count > 0 else 0

    def _get_specific_avg_comm(self, parent_task, child_task):
        """Calculates the average link delay only between eligible hosting routers."""
        
        # Check if we already calculated this specific edge
        edge_key = (parent_task, child_task)
        if not hasattr(self, '_edge_comm_cache'):
            self._edge_comm_cache = {}
        if edge_key in self._edge_comm_cache:
            return self._edge_comm_cache[edge_key]

        parent_nodes = list(self.comp_matrix.get(parent_task, {}).keys())
        child_nodes = list(self.comp_matrix.get(child_task, {}).keys())

        # If either task has no eligible nodes, communication is effectively 0/impossible
        if not parent_nodes or not child_nodes:
            return 0

        total_delay = 0
        count = 0
        
        # The M x M loop
        for p_node in parent_nodes:
            for c_node in child_nodes:
                delay = self.delay_matrix[p_node][c_node]
                if delay != math.inf:
                    total_delay += delay
                    count += 1

        # Cache and return the result
        avg_delay = total_delay / count if count > 0 else 0
        self._edge_comm_cache[edge_key] = avg_delay
        return avg_delay

    def _get_avg_comp(self, task):
        """Calculates average computation cost strictly across eligible nodes."""
        valid_costs = self.comp_matrix.get(task, {}).values()
        if not valid_costs:
            return 0 
        return sum(valid_costs) / len(valid_costs)


    # helper functions for calculating SLR (service latency ratio)
    def _get_min_comp(self, task):
        """Calculates the minimum computation cost strictly across eligible nodes."""
        valid_costs = self.comp_matrix.get(task, {}).values()
        if not valid_costs:
            return 0 
        return min(valid_costs)
    def calculate_cp_min(self):
        """Calculates CP_min: the longest path in the DAG using only minimum computation costs."""
        rank_min = {}
        
        # Recursive function to find the longest path to an exit node
        def calc_rank_min(task):
            if task in rank_min: return rank_min[task]
            max_succ = 0
            for succ in self.dag.get(task, []):
                max_succ = max(max_succ, calc_rank_min(succ))
            
            rank_min[task] = self._get_min_comp(task) + max_succ
            return rank_min[task]

        # Compute for all tasks
        for t in self.tasks:
            calc_rank_min(t)
            
        # CP_min is the maximum value found (the length of the critical path from entry to exit)
        if not rank_min:
            return 0
        return max(rank_min.values())
    def get_makespan(self, schedule):
        """Returns the total makespan of a given schedule."""
        if not schedule:
            return 0
        return max(end for node, start, end in schedule.values())




    # --- ALGORITHMS ---

    def compute_ranks(self):
        self.rank_u = {}
        self.rank_d = {}
        
        # Upward Rank (computed from exit nodes to entry nodes)
        def calc_upward(task):
            if task in self.rank_u: return self.rank_u[task]
            max_succ = 0
            for succ in self.dag[task]:
                max_succ = max(max_succ, self.avg_comm + calc_upward(succ))    # this uses the average of all links in the entire topology
            self.rank_u[task] = self._get_avg_comp(task) + max_succ
            return self.rank_u[task]

        for t in self.tasks: calc_upward(t)
            
        # Downward Rank (computed from entry nodes to exit nodes)
        def calc_downward(task):
            if task in self.rank_d: return self.rank_d[task]
            if not self.dag_parents[task]: 
                self.rank_d[task] = 0
                return 0
            max_pred = 0
            for pred in self.dag_parents[task]:
                max_pred = max(max_pred, calc_downward(pred) + self._get_avg_comp(pred) + self.avg_comm)
            self.rank_d[task] = max_pred
            return self.rank_d[task]

        for t in self.tasks: calc_downward(t)


    def compute_ranks_cabeee(self):
        """Uses the average of all links between two specific services, rather than average of all links in the entire topology.
        i.e.: uses mean shortest-path delay over only the routers that can actually host the parent × routers that can host the child, computed per edge"""
        
        self.rank_u = {}
        self.rank_d = {}
        
        # Upward Rank (computed from exit nodes to entry nodes)
        def calc_upward(task):
            if task in self.rank_u: return self.rank_u[task]
            max_succ = 0
            for succ in self.dag[task]:
                specific_comm = self._get_specific_avg_comm(task, succ)         # this uses the average of all links between two specific services
                max_succ = max(max_succ, specific_comm + calc_upward(succ))
            self.rank_u[task] = self._get_avg_comp(task) + max_succ
            return self.rank_u[task]

        for t in self.tasks: calc_upward(t)
            
        # Downward Rank (computed from entry nodes to exit nodes)
        def calc_downward(task):
            if task in self.rank_d: return self.rank_d[task]
            if not self.dag_parents[task]: 
                self.rank_d[task] = 0
                return 0
            max_pred = 0
            for pred in self.dag_parents[task]:
                max_pred = max(max_pred, calc_downward(pred) + self._get_avg_comp(pred) + self.avg_comm)
            self.rank_d[task] = max_pred
            return self.rank_d[task]

        for t in self.tasks: calc_downward(t)



    def compute_ranks_cabeee_mod1(self):
        """cabeee ranks, but each task is also charged its most expensive input transfer."""
        self.rank_u = {}
        self.rank_d = {}

        def max_input_comm(task):
            # Highest incoming (parent -> task) communication cost of all in-edges
            parents = self.dag_parents.get(task, [])
            if not parents:
                return 0
            return max(self._get_specific_avg_comm(p, task) for p in parents)

        # Upward Rank (computed from exit nodes to entry nodes)
        def calc_upward(task):
            if task in self.rank_u: return self.rank_u[task]
            max_succ = 0
            for succ in self.dag[task]:
                specific_comm = self._get_specific_avg_comm(task, succ)         # this uses the average of all links between two specific services
                max_succ = max(max_succ, specific_comm + calc_upward(succ))
            # mod1: add the highest input cost of this task on top of the cabeee rank
            self.rank_u[task] = self._get_avg_comp(task) + max_input_comm(task) + max_succ
            return self.rank_u[task]

        for t in self.tasks: calc_upward(t)

        # Downward Rank (computed from entry nodes to exit nodes)
        def calc_downward(task):
            if task in self.rank_d: return self.rank_d[task]
            if not self.dag_parents[task]:
                self.rank_d[task] = 0
                return 0
            max_pred = 0
            for pred in self.dag_parents[task]:
                max_pred = max(max_pred, calc_downward(pred) + self._get_avg_comp(pred) + self.avg_comm)
            self.rank_d[task] = max_pred
            return self.rank_d[task]

        for t in self.tasks: calc_downward(t)

    def compute_ranks_cabeee_mod2(self, schedule=None):
        """cabeee ranks. If a schedule is given, every task that was placed uses the
        makespan on its ASSIGNED node instead of the average over all eligible nodes."""
        self.rank_u = {}
        self.rank_d = {}

        def comp_cost(task):
            if schedule and task in schedule:
                assigned_node = schedule[task][0]
                # Fall back to the average if the assigned node somehow has no entry
                return self.comp_matrix.get(task, {}).get(assigned_node, self._get_avg_comp(task))
            return self._get_avg_comp(task)

        # Upward Rank (computed from exit nodes to entry nodes)
        def calc_upward(task):
            if task in self.rank_u: return self.rank_u[task]
            max_succ = 0
            for succ in self.dag[task]:
                specific_comm = self._get_specific_avg_comm(task, succ)         # this uses the average of all links between two specific services
                max_succ = max(max_succ, specific_comm + calc_upward(succ))
            self.rank_u[task] = comp_cost(task) + max_succ
            return self.rank_u[task]

        for t in self.tasks: calc_upward(t)

        # Downward Rank (computed from entry nodes to exit nodes)
        def calc_downward(task):
            if task in self.rank_d: return self.rank_d[task]
            if not self.dag_parents[task]:
                self.rank_d[task] = 0
                return 0
            max_pred = 0
            for pred in self.dag_parents[task]:
                max_pred = max(max_pred, calc_downward(pred) + comp_cost(pred) + self.avg_comm)
            self.rank_d[task] = max_pred
            return self.rank_d[task]

        for t in self.tasks: calc_downward(t)




    def schedule_heft(self):
        self.compute_ranks()
        # Sort by upward rank descending. rank_u(parent) is always greater than
        # rank_u(child), so this ordering is inherently topological.
        ordered_tasks = sorted(self.tasks, key=lambda x: self.rank_u[x], reverse=True)
        return self._place_tasks(ordered_tasks)

    def schedule_heft_cabeee(self):
        self.compute_ranks_cabeee()
        # Sort by upward rank descending
        ordered_tasks = sorted(self.tasks, key=lambda x: self.rank_u[x], reverse=True)
        return self._place_tasks(ordered_tasks)

    def schedule_heft_cabeee_mod1(self):
        self.compute_ranks_cabeee_mod1()
        # Sort by upward rank descending
        ordered_tasks = sorted(self.tasks, key=lambda x: self.rank_u[x], reverse=True)
        return self._place_tasks(ordered_tasks)

    def schedule_heft_cabeee_mod2(self, max_iterations=None):
        """Runs cabeee, then re-ranks using the computation cost each task actually got on
        its assigned node, re-placing until the task priority order stops changing.
        Returns (schedule, iterations) where iterations counts the placement passes."""
        if max_iterations is None:
            max_iterations = self.max_heft_iterations

        # Pass 1: no schedule yet, so this is exactly the cabeee ranking
        self.compute_ranks_cabeee_mod2()
        ordered_tasks = sorted(self.tasks, key=lambda x: self.rank_u[x], reverse=True)
        schedule = self._place_tasks(ordered_tasks)
        iterations = 1

        while iterations < max_iterations:
            # Re-rank with the makespan of each task on the node it was placed on
            self.compute_ranks_cabeee_mod2(schedule)
            new_order = sorted(self.tasks, key=lambda x: self.rank_u[x], reverse=True)

            if new_order == ordered_tasks:
                break   # priorities did not change -> converged, the schedule would repeat

            ordered_tasks = new_order
            schedule = self._place_tasks(ordered_tasks)
            iterations += 1

        return schedule, iterations

    def schedule_exhaustive(self, max_evaluations=None):
        """Exhaustively searches EVERY combination of task placements AND every valid
        ordering of tasks that share a node, and returns the schedule with the lowest
        makespan.

        A fixed, single topological order (as a prior version of this search used) is not
        enough: two tasks with no dependency between them can still be forced onto the
        same node, and if the search always ran them in one predetermined order, it would
        never consider slotting the later-in-order-but-independent one into an earlier
        idle gap on that node. That is a real gap, not a theoretical one - CPOP's own
        (differently tie-broken) topological order does exactly this kind of reordering
        and has been observed to beat this search's old fixed-order result by finding a
        schedule this search never even visited. So at every step the search branches over
        BOTH which currently-ready task to place next AND which node to place it on.

        "Ready" means every placeable predecessor has already been placed - predecessors
        with no eligible node anywhere are skipped, matching _earliest_start()/_place_tasks().
        Every ready task is branched on, with no symmetry breaking by node-contention
        group. Grouping tasks that can never share a node and forcing a fixed order
        between groups LOOKS safe and is not: a cross-group dependency can hold one group
        member back until after a group it was forced to follow has been placed, so the
        interleaving where it runs first on their shared node is never explored - the
        exact class of omission this search exists to avoid.

        The search is a depth-first branch and bound rather than a flat product loop: a
        partial placement is abandoned as soon as its makespan lower bound is no better
        than the best complete schedule found so far. Ordering the candidate nodes
        cheapest-first, and seeding the incumbent with the best schedule any heuristic
        produces, makes that pruning bite early.

        Sets self.exhaustive_evaluations (placements examined) and self.exhaustive_complete
        (False if the evaluation budget ran out before the search finished, in which case
        the result is the best schedule found rather than a proven optimum)."""
        if max_evaluations is None:
            max_evaluations = self.max_exhaustive_evaluations

        chain_after = self._min_chain_after()

        # Tasks with no eligible node cannot be placed at all (same as the heuristics).
        # Kept as a list in self.tasks order: the branch order decides which schedule is
        # returned when several tie on makespan, and iterating a set of task names would
        # make that depend on Python's per-process string hash seed.
        placeable = []
        placeable_set = set()
        for task in self.tasks:
            if self.comp_matrix.get(task):
                placeable.append(task)
                placeable_set.add(task)
            else:
                print(f"Warning: Task {task} could not be scheduled (No eligible nodes).")

        # Only placeable predecessors gate readiness or contribute an arrival delay - an
        # unplaceable predecessor is skipped entirely, exactly like _earliest_start().
        placeable_parents = {t: [p for p in self.dag_parents.get(t, []) if p in placeable_set] for t in placeable}
        placeable_children = {t: [] for t in placeable}
        for t in placeable:
            for p in placeable_parents[t]:
                placeable_children[p].append(t)

        # Cheapest node first: finds good schedules early, which prunes harder
        options = {t: sorted(self.comp_matrix[t].items(), key=lambda kv: kv[1]) for t in placeable}

        combinations = 1
        for opt in options.values():
            combinations *= len(opt)
        self.exhaustive_combinations = combinations
        self.exhaustive_evaluations = 0
        self.exhaustive_complete = True

        # Seed the incumbent with the best schedule every heuristic can produce. Two
        # reasons: a tight incumbent prunes the very first branches hard, and if the
        # evaluation budget runs out the result returned is still no worse than any
        # heuristic - without this, a truncated search can report a makespan that one of
        # the heuristics it is supposed to be the ground truth for already beat.
        best = {"makespan": math.inf, "schedule": None}
        for seed_schedule in (self.schedule_heft(),
                              self.schedule_heft_cabeee(),
                              self.schedule_heft_cabeee_mod1(),
                              self.schedule_heft_cabeee_mod2()[0],
                              self.schedule_cpop()):
            if not seed_schedule:
                continue
            seed_makespan = self.get_makespan(seed_schedule)
            if seed_makespan < best["makespan"]:
                best["makespan"] = seed_makespan
                best["schedule"] = seed_schedule

        avail = {n: 0 for n in self.nodes}
        placement = {} # task -> (node, start_time, end_time)
        indegree = {t: len(placeable_parents[t]) for t in placeable}
        n_tasks = len(placeable)

        def search(ready, makespan_so_far, bound_so_far):
            if len(placement) == n_tasks:
                if makespan_so_far < best["makespan"]:
                    best["makespan"] = makespan_so_far
                    best["schedule"] = dict(placement)
                return

            for task in list(ready):
                preds = placeable_parents[task]
                tail = chain_after[task]

                for node, comp_time in options[task]:
                    if self.exhaustive_evaluations >= max_evaluations:
                        self.exhaustive_complete = False
                        return
                    self.exhaustive_evaluations += 1

                    # Earliest start on this node given everything placed so far
                    est = avail[node]
                    for pred in preds:
                        pred_node, _, pred_aft = placement[pred]
                        arrival = pred_aft + self.delay_matrix[pred_node][node]
                        if arrival > est:
                            est = arrival

                    eft = est + comp_time
                    makespan = makespan_so_far if makespan_so_far > eft else eft

                    # Lower bound: nothing already committed can shrink, and every successor
                    # chain of this task still has to run after it finishes
                    bound = bound_so_far
                    if makespan > bound: bound = makespan
                    if eft + tail > bound: bound = eft + tail

                    if bound >= best["makespan"]:
                        continue # this branch cannot beat the incumbent - prune it

                    previous_avail = avail[node]
                    avail[node] = eft
                    placement[task] = (node, est, eft)
                    ready.remove(task)
                    newly_ready = []
                    for child in placeable_children[task]:
                        indegree[child] -= 1
                        if indegree[child] == 0:
                            ready.append(child)
                            newly_ready.append(child)

                    search(ready, makespan, bound)

                    for child in newly_ready:
                        ready.remove(child)
                    # Every child's indegree decrement above must be undone on backtrack,
                    # not just the ones that crossed zero - otherwise a child sharing this
                    # task as one of several parents keeps a stale (too-low) indegree the
                    # next time this task is tried on a different node, and can become
                    # "ready" before all of its real predecessors are placed.
                    for child in placeable_children[task]:
                        indegree[child] += 1
                    ready.append(task)
                    del placement[task]
                    avail[node] = previous_avail

                    if not self.exhaustive_complete:
                        return

        initial_ready = [t for t in placeable if indegree[t] == 0]
        search(initial_ready, 0, 0)

        return best["schedule"]

    def schedule_cpop(self):
        self.compute_ranks()
        priority = {t: self.rank_u[t] + self.rank_d[t] for t in self.tasks}
        
        # Identify Critical Path
        entry_nodes = [t for t in self.tasks if not self.dag_parents[t]]
        cp_node = max(entry_nodes, key=lambda x: priority.get(x, 0))
        critical_path = [cp_node]
        
        while self.dag.get(cp_node):
            cp_node = max(self.dag[cp_node], key=lambda x: priority.get(x, 0))
            critical_path.append(cp_node)
            
        # Select Critical Path Processor (minimizes sum of CP task computation times for tasks it CAN run)
        best_cp_proc, min_cp_cost = None, math.inf
        for node in self.nodes:
            cost = 0
            capable = False
            for t in critical_path:
                if node in self.comp_matrix.get(t, {}):
                    cost += self.comp_matrix[t][node]
                    capable = True
            if capable and cost < min_cp_cost:
                min_cp_cost = cost
                best_cp_proc = node

        # Walk the DAG in topological order, breaking ties by CPOP priority, rather than
        # sorting on priority alone. rank_u + rank_d is CONSTANT along the critical path
        # by construction, so a plain priority sort leaves the whole critical path tied
        # and lets floating-point noise order a task ahead of its own ancestors - which
        # silently drops that dependency and reports an impossibly low makespan.
        ordered_tasks = self._topological_order(priority)
        avail = {n: 0 for n in self.nodes}
        schedule = {}

        for task in ordered_tasks:
            best_node, min_eft, best_est = None, math.inf, 0

            # Restrict to CP Processor if it's a CP task AND the CP processor is eligible to run it
            eligible_nodes = list(self.comp_matrix.get(task, {}).keys())
            if task in critical_path and best_cp_proc in eligible_nodes:
                target_nodes = [best_cp_proc]
            else:
                target_nodes = eligible_nodes

            for node in target_nodes:
                est = self._earliest_start(task, node, schedule, avail)

                comp_time = self.comp_matrix[task][node]
                eft = est + comp_time

                if eft < min_eft:
                    min_eft = eft
                    best_est = est
                    best_node = node

            if best_node is not None:
                schedule[task] = (best_node, best_est, min_eft)
                avail[best_node] = min_eft
            else:
                print(f"Warning: Task {task} could not be scheduled (No eligible nodes).")
            
        return schedule


    # --- A-Beam: step-wise beam search ordered by f = g + h ---

    def _dag_steps(self):
        """Splits the DAG into "steps" (ASAP levels): a task sits in the earliest step
        that is still later than every one of its predecessors, so step(t) = 0 when t has
        no placeable parent and 1 + max(step(parents)) otherwise. The number of steps is
        therefore the length of the longest dependency chain in the DAG.

        Because an edge always increases the level, no two tasks in the same step depend
        on each other - they are mutually independent and could in principle run in
        parallel. Unplaceable tasks (no eligible node anywhere) are left out, matching
        _earliest_start()/_place_tasks(). Tasks keep self.tasks order inside a step so the
        search is deterministic."""
        level = {}
        placeable_set = {t for t in self.tasks if self.comp_matrix.get(t)}

        def calc_level(task):
            if task in level: return level[task]
            parents = [p for p in self.dag_parents.get(task, []) if p in placeable_set]
            level[task] = 0 if not parents else 1 + max(calc_level(p) for p in parents)
            return level[task]

        for t in self.tasks:
            if t in placeable_set:
                calc_level(t)

        if not level:
            return []
        steps = [[] for _ in range(max(level.values()) + 1)]
        for t in self.tasks:
            if t in placeable_set:
                steps[level[t]].append(t)
        return steps

    def _get_specific_min_comm(self, parent_task, child_task):
        """Cheapest possible transfer for this edge: the MINIMUM shortest-path delay over
        the routers that can host the parent x the routers that can host the child.

        _get_specific_avg_comm() returns an average, which can overshoot the delay an
        actual placement pays. The A-Beam heuristic needs a value no placement can ever
        beat, so it uses this minimum instead."""
        edge_key = (parent_task, child_task)
        if not hasattr(self, '_edge_min_comm_cache'):
            self._edge_min_comm_cache = {}
        if edge_key in self._edge_min_comm_cache:
            return self._edge_min_comm_cache[edge_key]

        parent_nodes = list(self.comp_matrix.get(parent_task, {}).keys())
        child_nodes = list(self.comp_matrix.get(child_task, {}).keys())
        if not parent_nodes or not child_nodes:
            return 0

        best = math.inf
        for p_node in parent_nodes:
            for c_node in child_nodes:
                delay = self.delay_matrix[p_node][c_node]
                if delay < best:
                    best = delay
        if best == math.inf:
            best = 0
        self._edge_min_comm_cache[edge_key] = best
        return best

    def compute_ranks_min(self):
        """Admissible variant of the HEFT-cabeee upward rank, used as the A-Beam
        heuristic h. Three changes make it a strict lower bound on the time still needed
        from the moment a task starts:

          * every task is charged its CHEAPEST computation cost over its eligible nodes
            (_get_min_comp) instead of the average,
          * every edge is charged its CHEAPEST possible transfer
            (_get_specific_min_comm) instead of the average, and
          * a task takes the MINIMUM over its successors instead of the maximum.

        No real placement can finish the sub-DAG below a task faster than this, so
        f = g + h never overestimates the true makespan and the ranking stays
        admissible."""
        self.rank_min_u = {}
        placeable_set = {t for t in self.tasks if self.comp_matrix.get(t)}

        def calc_upward(task):
            if task in self.rank_min_u: return self.rank_min_u[task]
            successors = [s for s in self.dag.get(task, []) if s in placeable_set]
            if successors:
                tail = min(self._get_specific_min_comm(task, s) + calc_upward(s)
                           for s in successors)
            else:
                tail = 0
            self.rank_min_u[task] = self._get_min_comp(task) + tail
            return self.rank_min_u[task]

        for t in self.tasks:
            if t in placeable_set:
                calc_upward(t)

    def _abeam_f(self, placement, makespan, pending):
        """f = g + h for a partial placement.

        g is the makespan already committed by the tasks in `placement`. h is the extra
        time still unavoidably needed on top of g, so f = g + h collapses to

            f = max( g, max over unplaced u of ( est_lb(u) + rank_min_u(u) ) )

        which is the right form for a makespan (a max-metric, not a sum: work still to
        come can overlap with work already scheduled, so literally adding the two would
        overestimate and break admissibility).

        est_lb(u) is a forward lower bound on when u could possibly start - each
        predecessor's earliest finish plus that edge's cheapest transfer, with already
        placed predecessors contributing their real finish time. `pending` must be in
        topological order."""
        finish_lb = {t: entry[2] for t, entry in placement.items()}
        f = makespan

        for task in pending:
            est = 0
            for pred in self.dag_parents.get(task, []):
                if pred not in finish_lb:
                    continue # unplaceable predecessor, skipped like everywhere else
                arrival = finish_lb[pred] + self._get_specific_min_comm(pred, task)
                if arrival > est:
                    est = arrival
            finish_lb[task] = est + self._get_min_comp(task)
            chain_end = est + self.rank_min_u[task]
            if chain_end > f:
                f = chain_end

        return f

    def schedule_abeam(self, beam_width=None, max_step_combinations=None):
        """A-Beam: an A*-flavoured beam search that walks the DAG one "step" at a time.

        The DAG is split into steps by _dag_steps() (the critical path sets how many there
        are). At each step every hosting combination for that step's services is explored
        as a separate branch; each branch is scored by f = g + h, where g is the makespan
        committed so far and h is the admissible remaining-time estimate from
        compute_ranks_min(). Once the whole step has been expanded, the frontier is pruned
        down to the k branches with the lowest f, and the search moves to the next step.

        beam_width (k) may be an int for a constant width, or a callable
        k(step_index, total_steps) -> int for a schedule that varies with depth (wider
        early, narrower later). Defaults to self.abeam_beam_width.

        A step's full hosting product is enumerated whenever it is small enough
        (max_step_combinations, default self.abeam_max_step_combinations). It often is
        not: a map-reduce DAG with 15 independent services on 17 eligible routers each has
        17^15 ~ 2.9e18 combinations in a SINGLE step, which cannot be enumerated at any
        budget. Above the cap the step is instead expanded one service at a time, pruning
        the partial combinations back to k after each service. That explores the same
        space with the same scoring, just with the beam applied inside the step as well as
        at its boundary. self.abeam_steps_enumerated records how many steps got the exact
        treatment and self.abeam_complete is True only when every step did.

        Services within a step are mutually independent, so they are placed in self.tasks
        order; that order only matters when two of them land on the same node, where it
        decides which runs first."""
        if beam_width is None:
            beam_width = self.abeam_beam_width
        if max_step_combinations is None:
            max_step_combinations = self.abeam_max_step_combinations

        width_of = beam_width if callable(beam_width) else (lambda i, n: beam_width)

        steps = self._dag_steps()
        for task in self.tasks:
            if not self.comp_matrix.get(task):
                print(f"Warning: Task {task} could not be scheduled (No eligible nodes).")
        if not steps:
            self.abeam_expansions = 0
            self.abeam_steps_enumerated = 0
            self.abeam_complete = True
            return {}

        self.compute_ranks_min()

        # Cheapest node first, so the partial-combination prune inside a wide step keeps
        # sensible branches even before f has much to go on.
        options = {t: sorted(self.comp_matrix[t].items(), key=lambda kv: kv[1])
                   for step in steps for t in step}

        # Everything still unplaced after step i, in topological order (steps are
        # topological by construction), precomputed once for _abeam_f().
        pending_after = [[t for later in steps[i + 1:] for t in later] for i in range(len(steps))]

        self.abeam_expansions = 0
        self.abeam_steps_enumerated = 0
        self.abeam_complete = True

        # A branch is (f, makespan, placement, avail).
        beam = [(0, 0, {}, {n: 0 for n in self.nodes})]

        for i, step_tasks in enumerate(steps):
            k = max(1, int(width_of(i, len(steps))))

            combinations = 1
            for t in step_tasks:
                combinations *= len(options[t])
            exact = combinations <= max_step_combinations
            if exact:
                self.abeam_steps_enumerated += 1
            else:
                self.abeam_complete = False

            # Expand the step service by service. When the whole product fits under the
            # cap nothing is dropped mid-step, so this enumerates every combination; when
            # it does not, the partial branches are pruned back to k after each service.
            branches = beam
            for position, task in enumerate(step_tasks):
                grown = []
                remaining_in_step = step_tasks[position + 1:]
                for _f, makespan, placement, avail in branches:
                    for node, comp_time in options[task]:
                        self.abeam_expansions += 1

                        est = self._earliest_start(task, node, placement, avail)
                        eft = est + comp_time

                        new_placement = dict(placement)
                        new_placement[task] = (node, est, eft)
                        new_avail = dict(avail)
                        new_avail[node] = eft
                        new_makespan = makespan if makespan > eft else eft

                        pending = remaining_in_step + pending_after[i]
                        new_f = self._abeam_f(new_placement, new_makespan, pending)
                        grown.append((new_f, new_makespan, new_placement, new_avail))

                # Prune to the k lowest f. Skipped mid-step while the step is being
                # enumerated exactly, so that an exact step really does see every
                # combination before the beam closes at its boundary.
                mid_step = position < len(step_tasks) - 1
                if not (exact and mid_step):
                    grown.sort(key=lambda b: (b[0], b[1]))
                    grown = grown[:k]
                branches = grown

            beam = branches

        # Every branch is a complete schedule; return the one that actually finishes first
        best = min(beam, key=lambda b: b[1])
        return best[2]

    def _earliest_start(self, task, node, schedule, avail):
        """Earliest time `task` can start on `node`: the node's own availability, plus
        the arrival of every predecessor's result over the shortest path.

        A predecessor missing from `schedule` is only legitimate when it has no eligible
        node anywhere and so could not be scheduled at all. A predecessor that simply has
        not been placed YET means the task ordering is not topological: its dependency
        would be silently dropped, producing a schedule that violates precedence and an
        impossibly low makespan. That is a hard error rather than a silent skip."""
        est = avail[node]
        for pred in self.dag_parents.get(task, []):
            if pred not in schedule:
                if self.comp_matrix.get(pred):
                    raise ValueError(
                        f"Task ordering is not topological: '{task}' is being placed "
                        f"before its predecessor '{pred}'. Scheduling a task before its "
                        f"parent drops that dependency and understates the makespan.")
                continue # genuinely unschedulable predecessor (no eligible nodes)
            pred_node, _, pred_aft = schedule[pred]
            arrival = pred_aft + self.delay_matrix[pred_node][node]
            if arrival > est:
                est = arrival
        return est

    def _place_tasks(self, ordered_tasks):
        """Greedy earliest-finish-time placement of an already prioritized task list.
        Identical to the placement loop in schedule_heft()/schedule_heft_cabeee()."""
        avail = {n: 0 for n in self.nodes}
        schedule = {} # task -> (node, start_time, end_time)

        for task in ordered_tasks:
            best_node, min_eft, best_est = None, math.inf, 0

            # Only iterate over ELIGIBLE nodes for this specific task
            eligible_nodes = self.comp_matrix.get(task, {})

            for node, comp_time in eligible_nodes.items():
                est = self._earliest_start(task, node, schedule, avail)

                eft = est + comp_time
                if eft < min_eft:
                    min_eft = eft
                    best_est = est
                    best_node = node

            if best_node is not None:
                schedule[task] = (best_node, best_est, min_eft)
                avail[best_node] = min_eft
            else:
                print(f"Warning: Task {task} could not be scheduled (No eligible nodes).")

        return schedule



    def _topological_order(self, priority=None):
        """Kahn topological sort. Ties are broken by descending priority (cabeee rank_u by
        default), so the resulting order matches the HEFT task ordering whenever that
        ordering is itself topological - which keeps the exhaustive search comparable."""
        if priority is None:
            self.compute_ranks_cabeee()
            priority = dict(self.rank_u)

        indegree = {t: len(self.dag_parents.get(t, [])) for t in self.tasks}
        ready = [t for t in self.tasks if indegree[t] == 0]
        order = []

        while ready:
            ready.sort(key=lambda x: priority.get(x, 0), reverse=True)
            task = ready.pop(0)
            order.append(task)
            for child in self.dag.get(task, []):
                indegree[child] -= 1
                if indegree[child] == 0:
                    ready.append(child)

        if len(order) != len(self.tasks):
            # Not a DAG (should not happen); fall back to the raw task list
            print("Warning: DAG contains a cycle, exhaustive search is using the raw task order.")
            order = list(self.tasks)
        return order

    def _min_chain_after(self):
        """chain_after[t] = lower bound on the time still needed AFTER t finishes: the
        longest successor chain, each task counted at its cheapest computation cost and
        with all communication ignored. Used to prune the exhaustive search."""
        min_tail = {}

        def calc(task):
            if task in min_tail: return min_tail[task]
            longest_succ = 0
            for succ in self.dag.get(task, []):
                longest_succ = max(longest_succ, calc(succ))
            min_tail[task] = self._get_min_comp(task) + longest_succ
            return min_tail[task]

        for t in self.tasks: calc(t)

        chain_after = {}
        for t in self.tasks:
            successors = self.dag.get(t, [])
            chain_after[t] = max([min_tail[s] for s in successors]) if successors else 0
        return chain_after


'''
# --- Execution Entry Point ---
if __name__ == "__main__":
    # You can load this directly from the file in your environment
    #with open("../scenario_json/cascon_main/ndn-cabeee-8dag-nesco.json", "r") as f:
    #with open("ndn-cabeee-8dag-nesco.json", "r") as f:
    with open("heft_DAG.json", "r") as f:
        json_data = json.load(f)
        
    scheduler = EdgeScheduler(json_data)
    
    # Compute ranks explicitly so we can print them
    scheduler.compute_ranks()
   
    # Calculate the theoretical lower bound (CP_min)
    cp_min = scheduler.calculate_cp_min()
    print(f"=== Baseline Metrics ===")
    print(f"Theoretical CP_min: {cp_min} ns\n")
    
    print("=== Task Ranks ===")
    print(f"{'Task':<15} | {'Upward Rank':<15} | {'Downward Rank':<15}")
    print("-" * 52)
    for t in scheduler.tasks:
        u_rank = scheduler.rank_u.get(t, 0)
        d_rank = scheduler.rank_d.get(t, 0)
        print(f"{t:<15} | {u_rank:<15.2f} | {d_rank:<15.2f}")
    print()


    print("=== HEFT Schedule ===")
    heft_sched = scheduler.schedule_heft()
    for t in scheduler.tasks: 
        if t in heft_sched:
            node, start, end = heft_sched[t]
            print(f"Task: {t:15} | Node: {node:8} | Start: {start:10} ns | End: {end:10} ns")
    makespan_heft = scheduler.get_makespan(heft_sched)
    slr_heft = makespan_heft / cp_min if cp_min > 0 else 0
    print(f">> HEFT Makespan: {makespan_heft} ns | SLR: {slr_heft:.4f}\n")

    print("=== HEFT-cabeee Schedule ===")
    heft_cabeee_sched = scheduler.schedule_heft_cabeee()
    for t in scheduler.tasks: 
        if t in heft_cabeee_sched:
            node, start, end = heft_cabeee_sched[t]
            print(f"Task: {t:15} | Node: {node:8} | Start: {start:10} ns | End: {end:10} ns")
    makespan_cabeee = scheduler.get_makespan(heft_cabeee_sched)
    slr_cabeee = makespan_cabeee / cp_min if cp_min > 0 else 0
    print(f">> HEFT-cabeee Makespan: {makespan_cabeee} ns | SLR: {slr_cabeee:.4f}\n")

    print("=== CPOP Schedule ===")
    cpop_sched = scheduler.schedule_cpop()
    for t in scheduler.tasks:
        if t in cpop_sched:
            node, start, end = cpop_sched[t]
            print(f"Task: {t:15} | Node: {node:8} | Start: {start:10} ns | End: {end:10} ns")
    makespan_cpop = scheduler.get_makespan(cpop_sched)
    slr_cpop = makespan_cpop / cp_min if cp_min > 0 else 0
    print(f">> CPOP Makespan: {makespan_cpop} ns | SLR: {slr_cpop:.4f}\n")
'''

# --- Execution Entry Point (Batch Processor) ---

# CSV columns, shared by the worker and the writer in the parent process.
# All *_Time_ms columns are wall-clock milliseconds for that scheme alone, measured
# with time.perf_counter(). Milliseconds is the one scale that covers the whole range
# seen here: the HEFT variants finish in well under a millisecond on small DAGs, while
# a budget-hit exhaustive search runs for tens of seconds.
FIELDNAMES = [
    "Scenario_File",
    "Total_Tasks",
    "Total_Nodes",
    "CP_min_ns",
    "HEFT_Makespan_ns",
    "HEFT_SLR",
    "HEFT_Time_ms",
    "HEFT_Cabeee_Makespan_ns",
    "HEFT_Cabeee_SLR",
    "HEFT_Cabeee_Time_ms",
    "HEFT_Cabeee_mod1_Makespan_ns",
    "HEFT_Cabeee_mod1_SLR",
    "HEFT_Cabeee_mod1_Time_ms",
    "HEFT_Cabeee_mod2_Makespan_ns",
    "HEFT_Cabeee_mod2_SLR",
    "HEFT_Cabeee_mod2_iterations",
    "HEFT_Cabeee_mod2_Time_ms",
    "CPOP_Makespan_ns",
    "CPOP_SLR",
    "CPOP_Time_ms",
    "exhaustive_Makespan_ns",
    "exhaustive_SLR",
    "exhaustive_Status",
    "exhaustive_Time_ms",
    "A_Beam_Makespan_ns",
    "A_Beam_SLR",
    "A_Beam_Status",
    "A_Beam_Beam_Width",
    "A_Beam_Time_ms",
    "Setup_Time_ms",
    "Scenario_Time_ms"
]


def _stamp():
    """[HH:MM:SS] prefix for progress lines. The full start date is printed once in the
    run header, so the per-line stamp stays short."""
    return time.strftime("[%H:%M:%S]")


def _format_duration(seconds):
    """Human-readable elapsed time: sub-minute stays in seconds, longer runs get
    Hh Mm Ss so a multi-hour sweep is readable at a glance."""
    if seconds < 60:
        return f"{seconds:.2f}s"
    total = int(seconds)
    h, rem = divmod(total, 3600)
    m, s = divmod(rem, 60)
    if h:
        return f"{h}h {m:02d}m {s:02d}s"
    return f"{m}m {s:02d}s"

# SLR is the schedule-length-ratio.
# It is a normalized metric designed to measure scheduling efficiency independent of the size of the graph.
# It divides the actual makespan by the theoretical critical path time of the graph.
# The critical path represents the absolute minimum time required to complete the graph if you assume tasks run sequentially
# along the longest path, ignoring communication delays and assuming the fastest possible processing speeds.
# A smaller SLR means a more efficient algorithm.

# Shared across worker processes via the pool initializer: a counter of how many
# scenarios have started, and the total number of scenarios.
_started_counter = None
_total_scenarios = None
_beam_width = None


def _init_worker(started_counter, total_scenarios, beam_width=None):
    """Pool initializer: hand every worker process the shared start counter."""
    global _started_counter, _total_scenarios, _beam_width
    _started_counter = started_counter
    _total_scenarios = total_scenarios
    _beam_width = beam_width


def process_scenario(file_path, beam_width=None):
    """Runs every scheduling algorithm over a single JSON scenario file.

    This is the unit of work handed to each worker process, so it must be a
    module-level function (picklable). It reports its own "Starting" line as it
    begins on a core; the parent reports the matching "Finished" line.
    Returns a dict: {"file": <name>, "row": <csv row dict or None>,
    "warning": <str or None>, "error": <str or None>}.
    """
    file_name = os.path.basename(file_path)

    # Bump the shared "started" counter and announce this scenario as it begins.
    if _started_counter is not None:
        with _started_counter.get_lock():
            _started_counter.value += 1
            started_idx = _started_counter.value
        print(f"{_stamp()} Starting scenario {started_idx}/{_total_scenarios}: {file_name}", flush=True)

    scenario_t0 = time.perf_counter()
    try:
        with open(file_path, "r") as f:
            json_data = json.load(f)

        # Initialize scheduler. Setup is timed separately from the schemes: it covers the
        # JSON parse plus the Floyd-Warshall all-pairs delay matrix, which is shared work
        # none of the individual algorithms should be charged for.
        t0 = time.perf_counter()
        scheduler = EdgeScheduler(json_data)
        cp_min = scheduler.calculate_cp_min()   # theoretical lower bound
        time_setup = (time.perf_counter() - t0) * 1000.0

        # Run HEFT
        t0 = time.perf_counter()
        heft_sched = scheduler.schedule_heft()
        time_heft = (time.perf_counter() - t0) * 1000.0
        makespan_heft = scheduler.get_makespan(heft_sched)
        slr_heft = makespan_heft / cp_min if cp_min > 0 else 0

        # Run HEFT-cabeee (Your optimized version)
        t0 = time.perf_counter()
        heft_cabeee_sched = scheduler.schedule_heft_cabeee()
        time_cabeee = (time.perf_counter() - t0) * 1000.0
        makespan_cabeee = scheduler.get_makespan(heft_cabeee_sched)
        slr_cabeee = makespan_cabeee / cp_min if cp_min > 0 else 0

        # Run HEFT-cabeee_mod1 (Your optimized version with modification 1)
        t0 = time.perf_counter()
        heft_cabeee_mod1_sched = scheduler.schedule_heft_cabeee_mod1()
        time_cabeee_mod1 = (time.perf_counter() - t0) * 1000.0
        makespan_cabeee_mod1 = scheduler.get_makespan(heft_cabeee_mod1_sched)
        slr_cabeee_mod1 = makespan_cabeee_mod1 / cp_min if cp_min > 0 else 0

        # Run HEFT-cabeee_mod2 (Your optimized version with modification 2)
        t0 = time.perf_counter()
        heft_cabeee_mod2_sched, iterations_cabeee_mod2 = scheduler.schedule_heft_cabeee_mod2()
        time_cabeee_mod2 = (time.perf_counter() - t0) * 1000.0
        makespan_cabeee_mod2 = scheduler.get_makespan(heft_cabeee_mod2_sched)
        slr_cabeee_mod2 = makespan_cabeee_mod2 / cp_min if cp_min > 0 else 0

        # Run CPOP
        t0 = time.perf_counter()
        cpop_sched = scheduler.schedule_cpop()
        time_cpop = (time.perf_counter() - t0) * 1000.0
        makespan_cpop = scheduler.get_makespan(cpop_sched)
        slr_cpop = makespan_cpop / cp_min if cp_min > 0 else 0

        # Run the exhaustive search over every possible combination of placements.
        # NOTE: this time includes the five heuristic schedules the search runs internally
        # to seed its incumbent - that seeding is part of what the method costs.
        t0 = time.perf_counter()
        exhaustive_sched = scheduler.schedule_exhaustive()
        time_exhaustive = (time.perf_counter() - t0) * 1000.0
        makespan_exhaustive = scheduler.get_makespan(exhaustive_sched)
        slr_exhaustive = makespan_exhaustive / cp_min if cp_min > 0 else 0

        # Run A-Beam (step-wise beam search ordered by f = g + h)
        k = beam_width if beam_width is not None else _beam_width
        if k is not None:
            scheduler.abeam_beam_width = k
        t0 = time.perf_counter()
        abeam_sched = scheduler.schedule_abeam()
        time_abeam = (time.perf_counter() - t0) * 1000.0
        makespan_abeam = scheduler.get_makespan(abeam_sched)
        slr_abeam = makespan_abeam / cp_min if cp_min > 0 else 0

        elapsed_ms = (time.perf_counter() - scenario_t0) * 1000.0

        warning = None
        if not scheduler.exhaustive_complete:
            warning = (f"exhaustive search hit its budget of "
                       f"{scheduler.max_exhaustive_evaluations:,} evaluations. Reported "
                       f"makespan is the best found, NOT a proven optimum.")

        row = {
            "Scenario File": file_name,
            "Total Tasks": len(scheduler.tasks),
            "Total Nodes": len(scheduler.nodes),
            "CP min ns": cp_min,
            "HEFT Makespan ns": makespan_heft,
            "HEFT SLR": f"{slr_heft:.4f}",
            "HEFT Time ms": f"{time_heft:.3f}",
            "HEFT cabeee Makespan ns": makespan_cabeee,
            "HEFT cabeee SLR": f"{slr_cabeee:.4f}",
            "HEFT cabeee Time ms": f"{time_cabeee:.3f}",
            "HEFT cabeee mod1 Makespan ns": makespan_cabeee_mod1,
            "HEFT cabeee mod1 SLR": f"{slr_cabeee_mod1:.4f}",
            "HEFT cabeee mod1 Time ms": f"{time_cabeee_mod1:.3f}",
            "HEFT cabeee mod2 Makespan ns": makespan_cabeee_mod2,
            "HEFT cabeee mod2 SLR": f"{slr_cabeee_mod2:.4f}",
            "HEFT cabeee mod2 iterations": iterations_cabeee_mod2,
            "HEFT cabeee mod2 Time ms": f"{time_cabeee_mod2:.3f}",
            "CPOP Makespan ns": makespan_cpop,
            "CPOP SLR": f"{slr_cpop:.4f}",
            "CPOP Time ms": f"{time_cpop:.3f}",
            "exhaustive Makespan ns": makespan_exhaustive,
            "exhaustive SLR": f"{slr_exhaustive:.4f}",
            # 1 = the search finished, so the makespan is a proven optimum.
            # 0 = it ran out of evaluations, so it is only the best found.
            "exhaustive Status": 1 if scheduler.exhaustive_complete else 0,
            "exhaustive Time ms": f"{time_exhaustive:.3f}",
            "A_Beam Makespan ns": makespan_abeam,
            "A_Beam SLR": f"{slr_abeam:.4f}",
            # 1 = every DAG step had its full hosting product enumerated exactly.
            # 0 = at least one step was too wide and was expanded service by service.
            "A_Beam Status": 1 if scheduler.abeam_complete else 0,
            "A_Beam Beam Width": scheduler.abeam_beam_width,
            "A_Beam Time ms": f"{time_abeam:.3f}",
            "Setup Time ms": f"{time_setup:.3f}",
            "Scenario Time ms": f"{elapsed_ms:.3f}"
        }
        return {"file": file_name, "row": row, "warning": warning,
                "error": None, "elapsed_ms": elapsed_ms}

    except Exception as e:
        elapsed_ms = (time.perf_counter() - scenario_t0) * 1000.0
        return {"file": file_name, "row": None, "warning": None,
                "error": str(e), "elapsed_ms": elapsed_ms}


if __name__ == "__main__":
    # 1. Setup command line arguments
    parser = argparse.ArgumentParser(description="Run scheduling algorithms over a directory of JSON scenarios.")
    parser.add_argument("-d", "--dir", required=True, help="Directory containing JSON scenario files")
    parser.add_argument("-o", "--out", default="results.csv", help="Output CSV file name")
    parser.add_argument("-j", "--jobs", type=int, default=os.cpu_count(),
                        help="Number of worker processes / CPU cores to use in parallel "
                             "(default: all available cores). Use 1 to run serially.")
    parser.add_argument("-k", "--beam-width", type=int, default=None,
                        help="A-Beam beam width: how many branches survive the prune at "
                             "each DAG step (default: the EdgeScheduler default of 10). "
                             "Larger k searches more and runs slower.")
    parser.add_argument("-p", "--pattern", default="*.json",
                        help="Only run scenarios whose file name matches this glob pattern "
                             "(default: '*.json', i.e. every scenario in the directory). A "
                             "pattern with no wildcard is treated as a suffix, so "
                             "-p 1-noSD2-multicast.json runs every file ending in that. "
                             "Quote patterns containing * so the shell does not expand them.")
    args = parser.parse_args()

    # 2. Find the JSON files in the specified directory, then keep the ones matching
    #    the requested pattern. A pattern with no glob wildcard is a plain suffix.
    all_json_files = sorted(glob.glob(os.path.join(args.dir, "*.json")))
    if not all_json_files:
        print(f"No JSON files found in directory: {args.dir}")
        exit(1)

    pattern = args.pattern
    if not any(ch in pattern for ch in "*?["):
        pattern = "*" + pattern

    json_files = [f for f in all_json_files if fnmatch.fnmatch(os.path.basename(f), pattern)]
    if not json_files:
        print(f"No JSON files in {args.dir} match pattern: {args.pattern}")
        exit(1)

    workers = max(1, min(args.jobs, len(json_files)))
    print(f"Run started {time.strftime('%Y-%m-%d %H:%M:%S')}")
    if len(json_files) == len(all_json_files):
        print(f"Found {len(json_files)} JSON scenarios. Evaluating on {workers} core(s)...\n")
    else:
        print(f"Found {len(all_json_files)} JSON scenarios, {len(json_files)} match "
              f"'{args.pattern}'. Evaluating on {workers} core(s)...\n")

    # 3. Fan the scenarios out across worker processes. Each JSON file is an
    #    independent unit of work, so every scenario runs on its own core and the
    #    parent process collects the finished rows.
    #
    #    Rows are written to the CSV (and flushed) as each scenario finishes, so
    #    interrupting the run part way through still leaves a usable results file
    #    with every scenario completed so far. If the whole run finishes, the file
    #    is rewritten once at the end in sorted file order for a deterministic
    #    result.
    results = {}
    total = len(json_files)
    finished = 0
    interrupted = False
    started_counter = multiprocessing.Value('i', 0)

    csv_file = open(args.out, mode='w', newline='')
    writer = csv.DictWriter(csv_file, fieldnames=FIELDNAMES)
    writer.writeheader()
    csv_file.flush()

    run_t0 = time.perf_counter()
    scenario_seconds = 0.0   # summed per-scenario time, for the parallel-speedup line

    # The executor is driven manually rather than with a "with" block: on Ctrl-C we
    # want shutdown(cancel_futures=True) so the queued scenarios are dropped and the
    # run stops promptly. A plain "with" would call shutdown(wait=True), which drains
    # the entire remaining queue before exiting.
    executor = concurrent.futures.ProcessPoolExecutor(
        max_workers=workers,
        initializer=_init_worker,
        initargs=(started_counter, total, args.beam_width),
    )
    try:
        future_to_file = {
            executor.submit(process_scenario, fp): os.path.basename(fp)
            for fp in json_files
        }
        for future in concurrent.futures.as_completed(future_to_file):
            res = future.result()
            results[res["file"]] = res
            finished += 1
            took = res.get("elapsed_ms", 0.0)
            scenario_seconds += took / 1000.0
            print(f"{_stamp()} Finished scenario {finished}/{total} "
                  f"in {took / 1000.0:.2f}s: {res['file']}", flush=True)
            if res["error"] is not None:
                print(f"{_stamp()}   -> Error processing {res['file']}: {res['error']}")
                continue
            if res["warning"] is not None:
                print(f"{_stamp()}   -> WARNING ({res['file']}): {res['warning']}")
            if res["row"] is not None:
                writer.writerow(res["row"])
                csv_file.flush()
    except KeyboardInterrupt:
        # Ctrl-C in the parent only
        interrupted = True
    except concurrent.futures.process.BrokenProcessPool:
        # Ctrl-C from a terminal reaches the whole process group, so the workers die
        # first and the pool breaks before the parent sees its own KeyboardInterrupt
        interrupted = True
    finally:
        if interrupted:
            print(f"\n{_stamp()} Stopping (waiting for the scenarios already running to finish)...",
                  flush=True)
            executor.shutdown(wait=True, cancel_futures=True)
        else:
            executor.shutdown(wait=True)
        csv_file.close()

    run_elapsed = time.perf_counter() - run_t0

    if interrupted:
        print(f"\nInterrupted after {finished}/{total} scenarios in "
              f"{_format_duration(run_elapsed)}. "
              f"Partial results (unsorted) saved in: {args.out}")
        exit(1)

    # 4. Full run finished: rewrite the CSV in the original (sorted) file order so
    #    the output is deterministic regardless of the order the workers finished.
    with open(args.out, mode='w', newline='') as csv_file:
        writer = csv.DictWriter(csv_file, fieldnames=FIELDNAMES)
        writer.writeheader()
        for file_path in json_files:
            res = results.get(os.path.basename(file_path))
            if res is not None and res["row"] is not None:
                writer.writerow(res["row"])

    print(f"\nEvaluation complete! Results tabulated in: {args.out}")
    print(f"Run finished {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Total wall-clock time for all {total} scenarios: "
          f"{_format_duration(run_elapsed)} ({run_elapsed:.2f}s)")
    print(f"  summed scenario time : {_format_duration(scenario_seconds)}"
          f"  (mean {scenario_seconds / total:.2f}s per scenario)")
    if run_elapsed > 0:
        print(f"  parallel speedup     : {scenario_seconds / run_elapsed:.1f}x "
              f"on {workers} core(s)")