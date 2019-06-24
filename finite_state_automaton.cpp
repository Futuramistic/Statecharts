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
  //linking node to the next cluster
  int stateExtended;
  //first letter of new alphabet
  int alphabetConnector;
  //
  int statesNumber;
  Cluster(int states,int extended, int connector){
    statesNumber=states;
    stateExtended=extended;
    alphabetConnector=connector;
  }
};

class finite_state_automaton{
  public:
  std::vector<Cluster*>* states;
  finite_automaton* result;
  std::vector<list<int>> acceptedWords;
  std::vector<std::vector<int>> statesUsed;
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
    set<int> sinks_set(getSinks(*result));
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
        if(sinks_set.find(oi->first)==sinks_set.end()){
          st << "\tnode [shape=record, style=\"\", color=black";
          st<<"];";
          st<< " q" << oi->first;
          st << ";\n";
        }
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
               st << "\tq" << stateAndTransitions.first << " -> q" << targetState << "\n";
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
      int sinksFound=0;
      st<<displayCluster(cluster,state,clustersShown);

      st<<"}\n";
      getStatesInfo();
    return st.str();
  }

  const string displayCluster(int cluster,int& statesShown,set<int>& clustersShown) const{
    stringstream st;

    st<<"\n\tsubgraph clusterR"<<cluster<<" {";
    int statesInCluster = 0;
    if(states->size()==0){
      for(int i=0;i<result->state_count;++i){
        st<<"q"<<i<<"; ";
      }
      return st.str();
    }
    if(cluster==0){
      st<<"q0; ";
      ++statesInCluster;
      ++statesShown;
      int statesNumber = 0;
      while(statesNumber!=statesShown){
        statesNumber=statesShown;
        for(int i=0;i<states->size();++i){
          if(statesShown==states->at(i)->stateExtended && clustersShown.find(i)==clustersShown.end()){
              clustersShown.insert(i);
              st<<displayCluster(i,statesShown,clustersShown);
          }
        }
      }
    }
    while(statesInCluster<states->at(cluster)->statesNumber){
      set<int> statesOfLetter;
      for(auto statesCluster=statesUsed.begin(); statesCluster!=statesUsed.end(); statesCluster++){
        if(statesShown<statesCluster->size()){
          statesOfLetter.insert(statesCluster->at(statesShown));
        }
      }
      for(int state: statesOfLetter){
        int statesNumber=0;
        bool cluster=false;
        while(statesNumber!=statesShown){
          statesNumber=statesShown;
          for(int i=0;i<states->size();i++){
            if(statesShown==states->at(i)->stateExtended && clustersShown.find(i)==clustersShown.end()){
                clustersShown.insert(i);
                st<<displayCluster(i,statesShown,clustersShown);
                cluster=true;
            }
          }
        }
        if(cluster){
          break;
        }
        st<<"q"<<state<<"; ";
        statesShown++;
        statesInCluster++;
      }
      if(statesInCluster==states->at(cluster)->statesNumber){
          bool shown = false;
          int statesNumber=0;
          while(statesNumber!=statesShown){
          statesNumber=statesShown;
          for(int i=0;i<states->size();i++){
            if(statesShown==states->at(i)->stateExtended && clustersShown.find(i)==clustersShown.end()){
                clustersShown.insert(i);
                shown=true;
                st<<"}\n";
                st<<displayCluster(i,statesShown,clustersShown);
              }
          }
        }
        if(!shown){
          st<<"}\n";
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
    cout<<"STATE USED IN WORDS: "<<endl;
    for(int i=0;i<statesUsed.size();i++){
      for(auto state=statesUsed.at(i).begin(); state!=statesUsed.at(i).end();state++){
        cout<<*state<<" ";
      }
      cout<<endl;
    }
  }

  void getAllStatesUsed(){
    statesUsed.clear();
    set<int> sinks = getSinks(*result);
    for(auto word = acceptedWords.begin(); word!=acceptedWords.end(); ++word){
      std::vector<int> wordStates;
      for(auto letter = word->begin(); letter!=word->end();++letter){
        set<int> letterStates = {0};
        result->run(letterStates, word->begin(), letter);
        wordStates.insert(wordStates.end(),letterStates.begin(),letterStates.end());
      }
      wordStates.push_back(1);
      wordStates.erase( std::unique( wordStates.begin(), wordStates.end() ), wordStates.end() );
      if(sinks.size()==0){
        statesUsed.push_back(wordStates);
      }
      else{
        for(auto sink: sinks){
          if(std::find(wordStates.begin(), wordStates.end(), *sink)==wordStates.end()){
            statesUsed.push_back(wordStates);
          }
        }
      }
    }
    statesUsed.erase( std::unique( statesUsed.begin(), statesUsed.end() ), statesUsed.end() );
  }

  bool nodeIsExpandable(int node){
    set<int> sinks = getSinks(*result);
    return sinks.find(node)==sinks.end() && node<result->state_count && node>0;
  }
};
