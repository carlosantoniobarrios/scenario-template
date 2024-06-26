/* -*- Mode:C++; c-file-style:"gnu"; indent-tabs-mode:nil; -*- */
/**
 * Copyright (c) 2011-2015  Regents of the University of California.
 *
 * This file is part of ndnSIM. See AUTHORS for complete list of ndnSIM authors and
 * contributors.
 *
 * ndnSIM is free software: you can redistribute it and/or modify it under the terms
 * of the GNU General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 *
 * ndnSIM is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * ndnSIM, e.g., in COPYING.md file.  If not, see <http://www.gnu.org/licenses/>.
 **/

// ndn-simple.cpp

#include "ns3/core-module.h"
#include "ns3/network-module.h"
#include "ns3/point-to-point-module.h"
#include "ns3/ndnSIM-module.h"

namespace ns3 {

/**
 * This scenario simulates a very simple network topology:
 *
 *
 *      +----------+     1Mbps      +-----------+     1Mbps      +----------+
 *      | consumer | <------------> | 3 routers | <------------> | producer |
 *      +----------+         10ms   +-----------+          10ms  +----------+
 *
 *
 * Consumer requests data from producer with frequency 10 interests per second
 * (interests contain constantly increasing sequence number).
 *
 * For every received interest, producer replies with a data packet, containing
 * 1024 bytes of virtual payload.
 *
 * To run scenario and see what is happening, use the following command:
 *
 *     NS_LOG=CustomAppConsumer:CustomAppProducer ./waf --run=ndn-cabeee-simple-app
 */

int
main(int argc, char* argv[])
{
  // setting default parameters for PointToPoint links and channels
  Config::SetDefault("ns3::PointToPointNetDevice::DataRate", StringValue("1Mbps"));
  Config::SetDefault("ns3::PointToPointChannel::Delay", StringValue("100ms"));
  Config::SetDefault("ns3::DropTailQueue<Packet>::MaxSize", StringValue("20p"));

  // Read optional command-line parameters (e.g., enable visualizer with ./waf --run=<> --visualize
  CommandLine cmd;
  cmd.Parse(argc, argv);

  // Creating nodes
  NodeContainer nodes;
  nodes.Create(5);

  // Connecting nodes using two links
  PointToPointHelper p2p;
  p2p.Install(nodes.Get(0), nodes.Get(1));
  p2p.Install(nodes.Get(1), nodes.Get(2));
  p2p.Install(nodes.Get(2), nodes.Get(3));
  p2p.Install(nodes.Get(3), nodes.Get(4));

  // Install NDN stack on all nodes
  ndn::StackHelper ndnHelper;
  ndnHelper.setPolicy("nfd::cs::lru");
  //ndnHelper.setCsSize(100);
  ndnHelper.setCsSize(1); // disable content store - doesn't seem to work.
  ndnHelper.SetDefaultRoutes(true);
  ndnHelper.InstallAll();


  // Choosing forwarding strategy
  //ndn::StrategyChoiceHelper::InstallAll("/prefix", "/localhost/nfd/strategy/multicast");
  ndn::StrategyChoiceHelper::InstallAll("/prefix", "/localhost/nfd/strategy/best-route");



  // Installing applications

  // App1
  ndn::AppHelper app1("CustomAppConsumer");
  app1.Install(nodes.Get(0)).Start(Seconds(0));

  // App2
  ndn::AppHelper app2("CustomAppProducer");
  app2.Install(nodes.Get(4)).Start(Seconds(0));



  Simulator::Stop(Seconds(10.0));

  ndn::L3RateTracer::InstallAll("rate-trace_cabeee-simple-app.txt", Seconds(0.1));
  ndn::CsTracer::InstallAll("cs-trace_cabeee_simple-app.txt", Seconds(0.1));
  ndn::AppDelayTracer::InstallAll("app-delays-trace_cabeee-simple-app.txt");

  Simulator::Run();
  Simulator::Destroy();

  return 0;
}

} // namespace ns3

int
main(int argc, char* argv[])
{
  return ns3::main(argc, argv);
}
