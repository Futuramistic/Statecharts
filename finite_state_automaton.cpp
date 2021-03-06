#include<libalf/conjecture.h>
#include <string>
#include <set>
#include <list>
#include <vector>
#include <map>
#include </home/matek/Desktop/H/DoomedDominatorsSinksAnalysis.cpp>
using namespace std;
using namespace libalf;

class Cluster{
  public:
  //States in cluster
  int statesNumber;
  //linking node to the next cluster
  int stateExtended;
  //first letter of new alphabet
  int alphabetConnector;
  Cluster(int states, int extended, int connector){
    statesNumber=states;
    stateExtended=extended;
    alphabetConnector=connector;
  }
};

class finite_state_automaton{
  public:
  std::vector<Cluster*>* states;
  finite_automaton* result;
  finite_state_automaton(){
    states = new std::vector<Cluster*>();
  }
  ~finite_state_automaton(){
    delete states;
  }

  string visualize() const
  {
    stringstream st;
    set<int>::iterator sti;
    map<int,int> nodesLabels;
    map<int,int> clusterLabels;
    nodesLabels[0]=-1;
    const set<int> sinks_set(getSinks(*result));
    st<<"digraph finite_state_machine{\n"
           "\tcompound=true;\n"
           "\trankdir=LR;\n"
           "\tnode [shape=\"record\"];\n";
      st<<"\n";
    //initial node
    for(sti = result->initial_states.begin(); sti != result->initial_states.end(); ++sti) {
       			st<< "\tnode [shape=plaintext, label=\"\", style=\"\"];";
       			st<< " iq" << *sti;
            st << ";\n";
    }

      //shown nodes
      map<int, bool>::const_iterator oi=result->output_mapping.begin();
      for(;oi!=result->output_mapping.end();++oi){
        st << "\tnode [shape=record, style=\"\", color=black";
        st<<"];";
        st<< " q" << oi->first;
        st << ";\n";
      }
      st<<"\n";
      //initial transition
      for(sti = result->initial_states.begin(); sti != result->initial_states.end(); ++sti)
       			st<< "\tiq" << *sti << " -> q" << *sti << " [color=blue];\n";

      //transitions
      set<int> clusterTransitions;
      for (const auto& stateAndTransitions : result->transitions)
        for (const auto& transition : stateAndTransitions.second)
          for (const auto& targetState : transition.second){
            bool notSinks = sinks_set.find(stateAndTransitions.first)==sinks_set.end() && sinks_set.find(targetState)==sinks_set.end();
             if(notSinks && targetState!=0){
                int state1position = 0;
                int state2position=result->state_count-targetState;
                if(stateAndTransitions.first!=0){
                  state1position=result->state_count-stateAndTransitions.first;
                }
                int cluster1 = getClusterState(state1position);
                int cluster2 = getClusterState(state2position);
                if(cluster1==cluster2){
                   st << "\tq" << stateAndTransitions.first << " -> q" << targetState << "\n";
                 }
                else{
                   st << "\tq" << stateAndTransitions.first << " -> q" << targetState << "[";
                   if(cluster2!=0&&cluster2!=-1){
                         st<<"lhead=\"clusterR"<<cluster2<<"\"";
                   }
                   if(cluster1!=0&&cluster1!=-1){
                         st<<"ltail=\"clusterR"<<cluster1<<"\"";
                         clusterLabels[cluster1]=transition.first;
                   }
                   st<<"];\n";
               }
               nodesLabels[targetState]=transition.first;
             }
           }
      //Nodes Labels
      for(auto label: nodesLabels){
        st<<"\tq"<<label.first<<"[label=\""<<label.second<<"\"];\n";
      }
      st<<"\n";

      //Show clusters
      oi=result->output_mapping.end();
      --oi;
      int cluster=0;
      int state=0;
      set<int> clustersShown;
      st<<displayCluster(cluster,oi,state,clustersShown,clusterLabels);

      st<<"}\n";
      getStatesInfo();
    return st.str();
  }

  const string displayCluster(int cluster, map<int, bool>::const_iterator& oi,int& statesShown,set<int>& clustersShown, map<int,int>& clusterLabels) const{
    stringstream st;
    int stateInCluster=0;
    st<<"\n\tsubgraph clusterR"<<cluster<<" {";
    int statesNumber = 0;
    //State 0 is unexpandable and always belongs to cluster 0
    if(cluster==0){
      st<<"q0; ";
      ++stateInCluster;
      ++statesShown;
      int statesNumber = 0;
      while(statesNumber!=statesShown){
        statesNumber=statesShown;
        for(int i=0;i<states->size();++i){
          if(statesShown==states->at(i)->stateExtended && clustersShown.find(i)==clustersShown.end()){
              clustersShown.insert(i);
              st<<displayCluster(i,oi,statesShown,clustersShown,clusterLabels);
          }
        }
      }
    }
    else{
      st<<"label=\""<<clusterLabels[cluster]<<"\";";
    }
    if(states->size()==0){
      while(oi!=result->output_mapping.begin()){
        st<<"q"<<oi->first<<"; ";
        --oi;
      }
      st<<"}\n";
    }
    else{
      while(stateInCluster<states->at(cluster)->statesNumber){
        int statesNumber = 0;
        while(statesNumber!=statesShown){
          statesNumber=statesShown;
          for(int i=0;i<states->size();++i){
            if(statesShown==states->at(i)->stateExtended && clustersShown.find(i)==clustersShown.end()){
                clustersShown.insert(i);
                st<<displayCluster(i,oi,statesShown,clustersShown,clusterLabels);
            }
          }
        }
        st<<"q"<<oi->first<<"; ";
        --oi;
        ++stateInCluster;
        ++statesShown;
        if(stateInCluster==states->at(cluster)->statesNumber){
          int statesNumber = 0;
          bool shown = false;
          while(statesNumber!=statesShown){
            statesNumber=statesShown;
            for(int i=0;i<states->size();++i){
              if(statesShown==states->at(i)->stateExtended && clustersShown.find(i)==clustersShown.end()){
                  clustersShown.insert(i);
                  shown=true;
                  st<<"}\n";
                  st<<displayCluster(i,oi,statesShown,clustersShown,clusterLabels);
              }
            }
          }
          if(!shown){
          st<<"}\n";
          }
        }
      }
    }
    return st.str();
  }

  const int getClusterState(int node) const{
    set<int> checked;
    return getClusterByState(node,0,checked,0);
  }

  const int getClusterByState(int& node, int cluster, set<int>& clustersChecked, int nodesChecked) const{
    if(states->size()==0){
      return -1;
    }
    int stateInClusterChecked=0;
    while(stateInClusterChecked<states->at(cluster)->statesNumber){
      int statesNumber = 0;
      while(statesNumber!=nodesChecked){
        statesNumber=nodesChecked;
        for(int i=0;i<states->size();i++){
          if(nodesChecked==states->at(i)->stateExtended && clustersChecked.find(i)==clustersChecked.end()){
              clustersChecked.insert(i);
              int check = getClusterByState(node,i,clustersChecked,nodesChecked);
              if(check!=-1){
                return check;
              }
              else{
                nodesChecked+=states->at(i)->statesNumber;
              }
          }
        }
      }
      if(nodesChecked==node){
        return cluster;
      }
      ++nodesChecked;
      ++stateInClusterChecked;
      if(stateInClusterChecked==states->at(cluster)->statesNumber){
        int statesNumber = 0;
        bool shown = false;
        while(statesNumber!=nodesChecked){
          statesNumber=nodesChecked;
          for(int i=0;i<states->size();i++){
            if(nodesChecked==states->at(i)->stateExtended && clustersChecked.find(i)==clustersChecked.end()){
              clustersChecked.insert(i);
              int check = getClusterByState(node,i,clustersChecked,nodesChecked);
              if(check!=-1){
                return check;
              }
              else{
                nodesChecked+=states->at(i)->statesNumber;
              }
            }
          }
        }
      }
    }
    return -1;
  }

  void getStatesInfo() const{
    cout<<"SINKS: ";
    for(auto sink: getSinks(*result)){
      cout<<sink<<" ,";
    }
    cout<<endl;
    cout<<"ACCEPTING: "<<getAcceptingState(*result)<<endl;
    cout<<"Doomed: ";
    for(auto sink: getDoomed(*result)){
      cout<<sink<<" ,";
    }
    cout<<endl;
    cout<<endl;
    cout<<"STATES: "<<endl;
    for(int i=0;i<states->size();i++){
      cout<<"STATE EXTENDED: "<<states->at(i)->stateExtended<<" , NODES IN CLUSTER: ";
      cout<<states->at(i)->statesNumber<<" , ALPHABET CONNECTOR: "<<states->at(i)->alphabetConnector<<endl<<endl;
    }
  }

  bool nodeIsExpandable(int node){
    set<int> sinks = getSinks(*result);
    return sinks.find(node)==sinks.end() && node<result->state_count && node>0;
  }
};
