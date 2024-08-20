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

// cabeee-dag-orchestratorB-app.hpp

#ifndef DAG_ORCHESTRATORB_APP_H_
#define DAG_ORCHESTRATORB_APP_H_

#include "ns3/ndnSIM/model/ndn-common.hpp"

#include "ns3/ndnSIM/apps/ndn-app.hpp"

#include <nlohmann/json.hpp>
using json = nlohmann::json;

#include <map>

namespace ns3 {

/**
 * @brief A simple custom application
 *
 * This applications demonstrates how to send Interests and respond with Datas to incoming interests
 *
 * When application starts it "sets interest filter" (install FIB entry) for /prefix/sub, as well as
 * sends Interest for this prefix
 *
 * When an Interest is received, it is replied with a Data with 1024-byte fake payload
 */
class DagOrchestratorB_App : public ndn::App {
public:
  // register NS-3 type "DagOrchestratorB_App"
  static TypeId
  GetTypeId();

  DagOrchestratorB_App();

  // (overridden from ndn::App) Processing upon start of the application
  virtual void
  StartApplication();

  // (overridden from ndn::App) Processing when application is stopped
  virtual void
  StopApplication();

  // (overridden from ndn::App) Callback that will be called when Interest arrives
  virtual void
  OnInterest(std::shared_ptr<const ndn::Interest> interest);

  // (overridden from ndn::App) Callback that will be called when Data arrives
  virtual void
  OnData(std::shared_ptr<const ndn::Data> contentObject);

private:
  void
  SendInterest(const std::string& interestName, std::string);
  
private:
  bool m_isRunning;
  ndn::Name m_prefix;
  ndn::Name m_name;
  //std::string m_nameUri;
  ndn::Name m_nameAndDigest;
  ndn::Name m_service;
  json m_dagOrchTracker; // with this data structure, we can keep track of WHICH inputs have arrived, rather than just the NUMBER of inputs. (in case one inputs arrives multiple times)
  json m_dagObject;
  //std::list <ndn::Name> m_listOfGeneratedInterests;
  ////std::map <std::string, std::vector<ndn::Block> > m_mapOfRxedBlocks;
  //std::map <std::string, std::vector<std::string> > m_mapOfRxedBlocks;
  //std::map <std::string, unsigned char> m_mapOfServiceInputs;
  std::vector <unsigned char> m_vectorOfServiceInputs;   // keeps a vector of ALL received results (to feed downstream service inputs)
  unsigned char m_serviceInputIndex;
  std::list <std::string> m_listOfServicesWithInputs;   // keeps track of which services have inputs
  std::list <std::string> m_listOfRootServices;         // keeps track of which services don't have any inputs
  std::list <std::string> m_listOfSinkNodes;            // keeps track of which node doesn't have an output (usually this is just the consumer)
};

} // namespace ns3

#endif // DAG_ORCHESTRATORB_APP_H_
