#include <iostream>
#include <string>
#include <list>
#include <libalf/alf.h>
#include <libalf/algorithm_angluin.h>
#include <libalf/conjecture.h>
#include <libalf/knowledgebase.h>
#include </home/matek/Desktop/H/teacher.cpp>
#include </home/matek/Desktop/H/finite_state_automaton.cpp>

#include <libalf/statistics.h>
class Learner{
  public:
    knowledgebase<bool> base;
    finite_state_automaton* automata;
    Teacher* teacher;
    Learner(int size){
      teacher = new Teacher(size);
      automata = new finite_state_automaton();
    }

    ~Learner(){
      delete teacher;
      delete automata;
    }

    void expand(int node){
      int oldAlphabetSize = teacher->getAlphabetSize();
      teacher->expandAlphabet();
      int change = teacher->getAlphabetSize()-oldAlphabetSize;
      if(automata->states->size()==0){
        if(getSinks(*automata->result).size()>0){
        automata->states->push_back(new Cluster(automata->result->state_count-1,-1,0));
        automata->states->at(0)->sink=true;
        }
        else{
        automata->states->push_back(new Cluster(automata->result->state_count,-1,0));
        }
      }
      //Save previously smallest accepted word and clear knowledge
      //list<int> acceptedWord = getSmallestAcceptedWord();
      base.clear_queries();
      base.clear();
      learn(true,node);
      automata->acceptedWords=getAcceptedWords();
      automata->getAllStatesUsed();
      int states = automata->result->state_count;
      int statesNotInCluster= 0;
      for(int i=0;i<automata->states->size();i++){
        statesNotInCluster+=automata->states->at(i)->statesNumber;
      }
      int statesInNewCluster=states-statesNotInCluster+1;
      if(getSinks(*automata->result).size()>0){
        --statesInNewCluster;
      }
      //UPDATE POSSIBLE SHIFTS
      for(int i=0;i<automata->states->size();i++){
          if(node<automata->states->at(i)->stateExtended){
            automata->states->at(i)->stateExtended+=statesInNewCluster-1;
          }
      }
      automata->updateFatherCluster(node);
      automata->states->push_back(new Cluster(statesInNewCluster,node,oldAlphabetSize));
      automata->markSinks();
      automata->clearGhostStates();
      automata->getStatesInfo();
    }

    /**
    *  Function to learn and expand automata
    *  Parameters are only used during the expansion to answer few queries automatically.
    **/
    void learn(bool expanding=false, int node=0, list<int> acceptedWord=list<int>()){
      Conjecture* result = NULL;
      angluin_simple_table<bool> algorithm(&base,NULL,teacher->getAlphabetSize());
      do {
        Conjecture * cj = algorithm.advance();
        if (cj == NULL) {
          list<list<int> > queries = base.get_queries();
          list<list<int> >::iterator li;
          for (li = queries.begin(); li != queries.end(); li++) {
            if(expanding&&tryToAnswer(*li,node,acceptedWord)){
              base.add_knowledge(*li, false);
            }
            else{
              bool a = teacher->answer_Membership(*li);
              base.add_knowledge(*li, a);
            }
          }
        }
        else {
          bool is_equivalent = teacher->check_Equivalence(cj);
          if (is_equivalent) {
            result = cj;
          } else {
            list<int> ce = teacher->get_CounterExample(teacher->alphabetsize);
            algorithm.add_counterexample(ce);
            delete cj;
          }
        }
      } while (result == NULL);
      automata->result = dynamic_cast<finite_automaton*>(result);
    }

    void display(){
      cout << endl << "Result: "<< endl<< automata->finite_state_automaton::visualize()<<endl;
    }

    void knowledge(){
      base.print(cout);
      for(auto kb=base.begin(); kb!=base.end(); ++kb){
        cout<<"Word: ";
        for(int i: kb->get_word()){
          cout<<i;
        }
        cout<<" , Response: "<<kb->get_answer()<<" ,Label: "<<kb->get_label();
        cout<<endl;
      }
    }

    /**
    * Try to answer returns true wether we know if the word can be rejected
    **/
    bool tryToAnswer(list<int>& word, int& node, list<int>& smallestAccepted){
      //New word has to be larger than the smallest previously accepted
      if(!hasMinimalPrefix(word,smallestAccepted,node)){
        return true;
      }
      if(goesThroughSink(word)){
        return true;
      }
      return false;
    }

    list<int> getSmallestAcceptedWord(){
      std::vector<list<int>> acceptedWords=getAcceptedWords();
      list<int> smallestAccepted=acceptedWords.at(0);
      for(int i=0; i<acceptedWords.size(); ++i){
        if(smallestAccepted.size()>acceptedWords.at(i).size()){
          smallestAccepted=acceptedWords.at(i);
        }
      }
      return smallestAccepted;
    }

    std::vector<list<int>> getAcceptedWords(){
      std::vector<list<int>> acceptedWords;
      for(auto kb=base.begin(); kb!=base.end(); ++kb){
        if(kb->get_answer()){
          acceptedWords.push_back(kb->get_word());
        }
      }
      for(auto kb=base.qbegin(); kb!=base.qend(); ++kb){
        if(kb->get_answer()){
          acceptedWords.push_back(kb->get_word());
        }
      }
      return acceptedWords;
    }

    bool hasMinimalPrefix(list<int>& word, list<int>& minimalWord, int& node) const{
      int minimalNodeExpanded = automata->states->at(0)->stateExtended;
      for(int i=0; i<automata->states->size(); ++i){
        if(minimalNodeExpanded>automata->states->at(i)->stateExtended){
          minimalNodeExpanded=automata->states->at(i)->stateExtended;
        }
      }
      if(node<minimalNodeExpanded){
        minimalNodeExpanded=node;
      }
      auto mini = minimalWord.begin();
      auto check = word.begin();
      for(int i = 0; i<minimalNodeExpanded;++i){
        if(*mini!=*check){
          return false;
        }
        mini++;
        check++;
      }
      return true;
    }

    bool goesThroughSink(list<int> word){
        set<int> statesOfWord = {0};
        set<int> sinks = getSinks(*automata->result);
        if(sinks.size()==0){
          return false;
        }
        automata->result->run(statesOfWord,word.begin(),word.end());
        for(int state: statesOfWord){
          if(sinks.find(state)!=sinks.end()){
            return true;
          }
        }
        return false;
    }

    void mapping(){
      typename std::map<int, bool>::const_iterator oi;
      cout << endl << "Mapping: "<< endl;
      for(oi = automata->result->output_mapping.begin(); oi != automata->result->output_mapping.end(); ++oi)
      {
          cout<<"State ("<<oi->first<<"): "<<oi->second<<"| ";
      }
      cout<<endl;
    }

    bool checkIfNodeIsExpandable(int node){
      return automata->nodeIsExpandable(node);
    }
};
