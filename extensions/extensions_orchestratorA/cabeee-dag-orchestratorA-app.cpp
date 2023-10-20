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

// The orchestrator should receive the interest from the consumer (with JSON DAG as a parameter), read the DAG workflow, and use it to
// coordinate interest generation.
// Start with an interest for the root service(s) - the most upstream service(s)!!
// Keep track of received data packets (results) for each service.
// Once all results from upstream services are received, we can then generate the interest for the downstream service they feed.
// Eventually, respond to the consumer with the final data result.


// cabeee-dag-orchestratorA-app.cpp

#include "cabeee-dag-orchestratorA-app.hpp"

#include "ns3/ptr.h"
#include "ns3/log.h"
#include "ns3/simulator.h"
#include "ns3/packet.h"
#include "ns3/string.h"

#include "ns3/ndnSIM/helper/ndn-stack-helper.hpp"
#include "ns3/ndnSIM/helper/ndn-fib-helper.hpp"

#include "ns3/random-variable-stream.h"

//#include "ns3/ndnSIM/ndn-cxx/ndn-cxx/encoding/encoder.hpp"
//#include "ns3/ndnSIM/ndn-cxx/ndn-cxx/encoding/block.hpp"
//#include "ns3/ndnSIM/ndn-cxx/encoding/tlv.hpp"
//#include "ns3/ndnSIM/ndn-cxx/encoding/block-helpers.hpp"

#include <string.h>

#include <fstream>
#include <nlohmann/json.hpp>
using json = nlohmann::json;

NS_LOG_COMPONENT_DEFINE("DagOrchestratorAApp");

namespace ns3 {

NS_OBJECT_ENSURE_REGISTERED(DagOrchestratorAApp);

// register NS-3 type
TypeId
DagOrchestratorAApp::GetTypeId()
{
  static TypeId tid = TypeId("DagOrchestratorAApp")
    .SetParent<ndn::App>()
    .AddConstructor<DagOrchestratorAApp>()
    .AddAttribute("Prefix", "Requested name", StringValue("/dumb-interest"),
                    ndn::MakeNameAccessor(&DagOrchestratorAApp::m_name), ndn::MakeNameChecker())
    .AddAttribute("Service", "Requested service", StringValue("dumb-service"),
                    ndn::MakeNameAccessor(&DagOrchestratorAApp::m_service), ndn::MakeNameChecker());
  return tid;
}

DagOrchestratorAApp::DagOrchestratorAApp()
  : m_isRunning(false)
{
}

// Processing upon start of the application
void
DagOrchestratorAApp::StartApplication()
{
  // initialize ndn::App
  ndn::App::StartApplication();
  m_isRunning = true;

  // Add entry to FIB for `/prefix/sub`
  //ndn::FibHelper::AddRoute(GetNode(), "/prefix/sub", m_face, 0); //cabeee took this out, let the global router figure it out.
  ndn::FibHelper::AddRoute(GetNode(), m_name, m_face, 0);


  //m_mapOfInputTotals.clear();
  //m_mapOfRxedInputNums.clear();
  m_dagObject = 0;
  //m_dagTracker = 0;

  //DagOrchestratorAApp::SendInterest("/cabeee");
  // Schedule send of first interest
  //Simulator::Schedule(Seconds(1.0), &DagOrchestratorAApp::SendInterest, this);
  //Simulator::Schedule(Seconds(2.0), &DagOrchestratorAApp::SendInterest, this);
  //Simulator::Schedule(Seconds(3.0), &DagOrchestratorAApp::SendInterest, this);
  //Simulator::Schedule(Seconds(4.0), &DagOrchestratorAApp::SendInterest, this);
  //Simulator::Schedule(Seconds(5.0), &DagOrchestratorAApp::SendInterest, this);
  //Simulator::Schedule(Seconds(6.0), &DagOrchestratorAApp::SendInterest, this);
  //Simulator::Schedule(Seconds(7.0), &DagOrchestratorAApp::SendInterest, this);
  //Simulator::Schedule(Seconds(8.0), &DagOrchestratorAApp::SendInterest, this);
}

// Processing when application is stopped
void
DagOrchestratorAApp::StopApplication()
{
  m_isRunning = false;
  // cleanup ndn::App
  ndn::App::StopApplication();
}





void
DagOrchestratorAApp::SendInterest(const std::string& interestName, std::string dagString)
{
  if (!m_isRunning)
  {
    NS_LOG_DEBUG("Warning: trying to send interest while application is stopped!");
    return;
  }

  /////////////////////////////////////
  // Sending one Interest packet out //
  /////////////////////////////////////

  // Create and configure ndn::Interest
  //auto interest = std::make_shared<ndn::Interest>("/prefix/sub");
  //auto interest = std::make_shared<ndn::Interest>(m_name); // must take it in as an argument, not just use m_name!!
  auto interest = std::make_shared<ndn::Interest>(interestName);
  Ptr<UniformRandomVariable> rand = CreateObject<UniformRandomVariable>();
  interest->setNonce(rand->GetValue(0, std::numeric_limits<uint32_t>::max()));
  interest->setInterestLifetime(ndn::time::seconds(5));
  //interest->setMustBeFresh(true);



  // overwrite the dag parameter "head" value and generate new application parameters (thus calculating new sha256 digest)
  //std::string dagString = std::string(reinterpret_cast<const char*>(dagParameter.value()), dagParameter.value_size());
  auto dagObject = json::parse(dagString);
  dagObject["head"] = interestName;
  std::string updatedDagString = dagObject.dump();
  // in order to convert from std::string to a char[] datatype we do the following (https://stackoverflow.com/questions/7352099/stdstring-to-char):
  char *dagStringParameter = new char[updatedDagString.length() + 1];
  strcpy(dagStringParameter, updatedDagString.c_str());
  size_t length = strlen(dagStringParameter);

  //add DAG workflow as a parameter to the new interest
  //interest->setApplicationParameters(dagParameter);

  //add modified DAG workflow as a parameter to the new interest
  interest->setApplicationParameters((const uint8_t *)dagStringParameter, length);



  NS_LOG_DEBUG("Orchestrator: Sending Interest packet for " << *interest);

  // Call trace (for logging purposes)
  m_transmittedInterests(interest, this, m_face);

  m_appLink->onReceiveInterest(*interest);
}

// Callback that will be called when Interest arrives
void
DagOrchestratorAApp::OnInterest(std::shared_ptr<const ndn::Interest> interest)
{
  ndn::App::OnInterest(interest);


  NS_LOG_DEBUG("Received Interest packet for " << interest->getName());
  //NS_LOG_DEBUG("Received on node hosting service " << m_service);

  


  // decode the DAG string contained in the application parameters, so we can generate the new interest(s)
  //extract custom parameter from interest packet
  auto dagParameterFromInterest = interest->getApplicationParameters();
  //std::string dagString = ndn::encoding::readString(dagParameterFromInterest);
  std::string dagString = std::string(reinterpret_cast<const char*>(dagParameterFromInterest.value()), dagParameterFromInterest.value_size());
  //std::string dagString = ndn::lp::DecodeHelper();
  //auto dagBuffer = dagParameterFromInterest.ndn::Block::getBuffer();
  //auto dagValue = dagParameterFromInterest.ndn::Block::value();
  ////NS_LOG_DEBUG("Interest parameters received: " << dagParameterFromInterest);
  //NS_LOG_DEBUG("Interest parameters received as string: " << dagString);
  ////NS_LOG_DEBUG("Interest parameters received as value: " << dagValue);






  // read the dag parameters and figure out which interest(s) to generate (only for those that don't have inputs coming from other services - "root" services).
  m_dagObject = json::parse(dagString);


  // here we generate just the first interest(s) according to the workflow (not backwards as done originally in our proposed optimized methodology).
  // to do this, we must discover which services in the DAG are "root" services (services which don't have inputs coming from other services - sensors excluded).


  for (auto& x : m_dagObject["dag"].items())
  {
    m_listOfRootServices.push_back(x.key()); // for now, add ALL keys to the list, we'll remove non-root ones later
    for (auto& y : m_dagObject["dag"][x.key()].items())
    {
      m_listOfServicesWithInputs.push_back(y.value()); // add all values to the list
      if ((std::find(m_listOfSinkNodes.begin(), m_listOfSinkNodes.end(), y.value()) == m_listOfSinkNodes.end())) // if y.value() does not exist in m_listOfSinkNodes
      {
        m_listOfSinkNodes.push_back(y.value()); // for now, add ALL values to the list, we'll remove non-sinks later
      }
    }
  }

  // now remove services that feed into other services from the list of sink nodes
  for (auto& x : m_dagObject["dag"].items())
  {
    if (!(std::find(m_listOfSinkNodes.begin(), m_listOfSinkNodes.end(), x.key()) == m_listOfSinkNodes.end())) // if x.key() exists in m_listOfSinkNodes
    {
      m_listOfSinkNodes.remove(x.key());
    }
  }

  // now remove services that have other services as inputs from the list of root services
  for (auto thisItem : m_listOfServicesWithInputs)
  {
    if (!(std::find(m_listOfRootServices.begin(), m_listOfRootServices.end(), thisItem) == m_listOfRootServices.end())) // if thisItem exists in m_listOfRootServices
    {
      m_listOfRootServices.remove(thisItem);
    }
  }




  for (auto thisItem : m_listOfRootServices)
  {
    // generate new interest for root services if one has not yet been generated
    NS_LOG_DEBUG("Generating interest for: " << thisItem);

    // We need to see if this interest has already been generated. If so, don't increment
    // if this is a new interest (if interest is not in our list of generated interests)
    //if ((std::find(m_listOfGeneratedInterests.begin(), m_listOfGeneratedInterests.end(), thisItem) == m_listOfGeneratedInterests.end())) { // if we don't find it...
      // add this new interest to list of generated interests
      //m_listOfGeneratedInterests.push_back(thisItem);
      DagOrchestratorAApp::SendInterest(thisItem, dagString);
    //}
  }


  // create the tracking data structure using JSON
  json nullJson;
  for (auto& x : m_dagObject["dag"].items()) // first pass just gets the source services (don't worry what they feed)
  {
    unsigned char isRoot = 0;
    if (!(std::find(m_listOfRootServices.begin(), m_listOfRootServices.end(), x.key()) == m_listOfRootServices.end())) // if x.key() exists in m_listOfRootServices
      isRoot = 1;
    m_dagTracker.push_back( json::object_t::value_type(x.key(), {{"root", isRoot}} ) );
    m_dagTracker[x.key()].push_back( json::object_t::value_type("interestGenerated", 0 ) );
    m_dagTracker[x.key()].push_back( json::object_t::value_type("inputsRxed", nullJson ) );
  }
  //std::cout << std::setw(2) << m_dagTracker << '\n';
  for (auto& x : m_dagObject["dag"].items())
  {
    for (auto& y : m_dagObject["dag"][x.key()].items())
    {
      if ((std::find(m_listOfSinkNodes.begin(), m_listOfSinkNodes.end(), y.value()) == m_listOfSinkNodes.end())) // if y.value() does not exist in m_listOfSinkNodes
      {
        m_dagTracker[(std::string)y.value()]["inputsRxed"][(std::string)x.key()] = 0;
        //std::cout << "x.key is " << x.key() << ", and y.value is " << y.value() << '\n';
      }
    }
  }
  //std::cout << "dagTracker data structure: " << std::setw(2) << m_dagTracker << '\n';


  m_nameAndDigest = interest->getName();  // store the name with digest so that we can later generate the final result data packet with the same name/digest!


  // Note that Interests send out by the app will not be sent back to the app !

  /*
  auto data = std::make_shared<ndn::Data>(interest->getName());
  data->setFreshnessPeriod(ndn::time::milliseconds(3000));
  data->setContent(std::make_shared< ::ndn::Buffer>(1024));
  ndn::StackHelper::getKeyChain().sign(*data);
  NS_LOG_DEBUG("Sending Data packet for " << data->getName());
  // Call trace (for logging purposes)
  m_transmittedDatas(data, this, m_face);
  m_appLink->onReceiveData(*data);
  */
}

// Callback that will be called when Data arrives
void
DagOrchestratorAApp::OnData(std::shared_ptr<const ndn::Data> data)
{
  NS_LOG_DEBUG("Receiving Data packet for " << data->getName());

  //std::cout << "DATA received for name " << data->getName() << std::endl;

  //std::cout << "mapOfRxedInputNums = " << m_mapOfRxedInputNums << std::endl;
  //std::cout << "content = " << data->getContent() << std::endl;

  std::string rxedDataName = (data->getName()).getPrefix(-1).toUri(); // remove the last component of the name (the parameter digest) so we have just the raw name


  // TODO: this is a HACK. I need a better way to get to the first byte of the content. Right now, I'm just incrementing the pointer past the TLV type, and size.
  // and then getting to the first byte (which is all I'm using for data)
  unsigned char serviceOutput = 0;
  uint8_t *pServiceInput = 0;
  //pServiceInput = (uint8_t *)(m_mapOfRxedBlocks.back().data());
  pServiceInput = (uint8_t *)(data->getContent().data()); // this points to the first byte, which is the TLV-TYPE (21 for data packet content)
  pServiceInput++;  // now this points to the second byte, containing 253 (0xFD), meaning size (1024) is expressed with 2 octets
  pServiceInput++;  // now this points to the first size octet
  pServiceInput++;  // now this points to the second size octet
  pServiceInput++;  // now we are pointing at the first byte of the true content
  m_mapOfServiceInputs[rxedDataName] = (*pServiceInput);





  // mark down this input as having been received for all services that use this data as an input
  for (auto& service : m_dagTracker.items())
  {
    for (auto& serviceInput : m_dagTracker[(std::string)service.key()]["inputsRxed"].items())
    {
      if (serviceInput.key() == rxedDataName)
      {
        serviceInput.value() = 1;
      }
    }
  }
  //std::cout << "Updated dagTracker data structure: " << std::setw(2) << m_dagTracker << '\n';





  // now we check to see which services that we have not generated interests for yet have all their inputs satisfied, and generate new interest if satisfied.
  // note there might be more than one service that needs to run next (ex: in the RPA DAG, when we receive R1, we can now run S2 AND S3)
  for (auto& service : m_dagTracker.items())  // for each service in the tracker
  {
    if (service.value()["interestGenerated"] == 0)  // if we haven't generated an interest for this service, then analyze its rxed inputs
    {
      unsigned char allInputsReceived = 1;
      for (auto& serviceInput : m_dagTracker[(std::string)service.key()]["inputsRxed"].items())
      {
        if (serviceInput.value() == 0)
        {
          allInputsReceived = 0;
          break;
        }
      }
      if (allInputsReceived == 1)
      {
        // generate the interest for this service, and mark it down as generated
        std::string dagString = m_dagObject.dump();
        DagOrchestratorAApp::SendInterest(service.key(), dagString);
        service.value()["interestGenerated"] = 1;
      }
    }
  }



  // if the result of the last service has been received, then generate data packet with the final result for the consumer.
  for (auto sinkNode : m_listOfSinkNodes)
  {
    //if this data packet feeds sink node
    //std::cout << "        CHECKING SINK: rxedData is " << rxedDataName << ", and current sink node is " << sinkNode << '\n';
    if (sinkNode == m_dagObject["dag"][rxedDataName])
    {
      NS_LOG_DEBUG("Final data packet! Creating data for name: " << m_nameAndDigest);   // m_name doesn't have the sha256 digest, so it doesn't match the original interest!
                                                                                        // We use m_nameAndDigest to store the old name with the digest.
      auto new_data = std::make_shared<ndn::Data>(m_nameAndDigest);
      new_data->setFreshnessPeriod(ndn::time::milliseconds(3000));

      new_data->setContent(data->getContent());
      ndn::StackHelper::getKeyChain().sign(*new_data);
      // Call trace (for logging purposes)
      m_transmittedDatas(new_data, this, m_face);
      m_appLink->onReceiveData(*new_data);

    }
  }

}

} // namespace ns3
