#!/usr/bin/env python3

import json
import re
import math

class EdgeScheduler:
    def __init__(self, json_data):
        self.nodes = []
        self.links = {}
        self.dag = {}
        self.tasks = []
        
        self.delay_matrix = {}
        self.comp_matrix = {} # comp_matrix[task][node] = time_in_ns
        
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

    def _get_avg_comp(self, task):
        """Calculates average computation cost strictly across eligible nodes."""
        valid_costs = self.comp_matrix.get(task, {}).values()
        if not valid_costs:
            return 0 
        return sum(valid_costs) / len(valid_costs)

    # --- ALGORITHMS ---

    def compute_ranks(self):
        self.rank_u = {}
        self.rank_d = {}
        
        # Upward Rank (computed from exit nodes to entry nodes)
        def calc_upward(task):
            if task in self.rank_u: return self.rank_u[task]
            max_succ = 0
            for succ in self.dag[task]:
                max_succ = max(max_succ, self.avg_comm + calc_upward(succ))
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

    def schedule_heft(self):
        self.compute_ranks()
        # Sort by upward rank descending
        ordered_tasks = sorted(self.tasks, key=lambda x: self.rank_u[x], reverse=True)
        
        avail = {n: 0 for n in self.nodes}
        schedule = {} # task -> (node, start_time, end_time)
        
        for task in ordered_tasks:
            best_node, min_eft, best_est = None, math.inf, 0
            
            # Only iterate over ELIGIBLE nodes for this specific task
            eligible_nodes = self.comp_matrix.get(task, {})
            
            for node, comp_time in eligible_nodes.items():
                est = avail[node]
                for pred in self.dag_parents.get(task, []):
                    if pred in schedule:
                        pred_node, _, pred_aft = schedule[pred]
                        transfer_time = self.delay_matrix[pred_node][node]
                        est = max(est, pred_aft + transfer_time)
                
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

        ordered_tasks = sorted(self.tasks, key=lambda x: priority[x], reverse=True)
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
                est = avail[node]
                for pred in self.dag_parents.get(task, []):
                    if pred in schedule:
                        pred_node, _, pred_aft = schedule[pred]
                        transfer_time = self.delay_matrix[pred_node][node]
                        est = max(est, pred_aft + transfer_time)
                
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

    print("\n=== CPOP Schedule ===")
    cpop_sched = scheduler.schedule_cpop()
    for t in scheduler.tasks:
        if t in cpop_sched:
            node, start, end = cpop_sched[t]
            print(f"Task: {t:15} | Node: {node:8} | Start: {start:10} ns | End: {end:10} ns")