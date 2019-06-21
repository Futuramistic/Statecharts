#include <iostream>
#include <string>
#include <list>
#include <libalf/alf.h>
using namespace std;
using namespace libalf;
class Teacher{

public:
  int alphabetsize;
  Teacher(int alphabetsize){
    this->alphabetsize=alphabetsize;
  }
  list<int> get_CounterExample(int alphabetsize) {
  	list<int> ce;
  	string c;

  	bool ok;
  	do {
  		ok = true;

  		cout << "Please enter a counter example: ";
  		cin >> c;

  		unsigned int i;
  		for (i = 0; i < c.length(); i++) {
  			if (c.at(i) < '0' || c.at(i) > ('0' + alphabetsize - 1)) {
  				cout << "Found illegal character " << c.at(i) << endl;
  				ok = false;
  				ce.clear();
  				break;
  			}
  			ce.push_back(c.at(i) - '0');
  		}
  	} while (!ok);
  	return ce;
  }
  bool check_Equivalence(Conjecture * cj) {

	// display the automaton
	if (cj != NULL) {
		finite_state_machine<int> * a = static_cast<finite_state_machine<int>*> (cj);
		cout << endl << "Conjecture:" << endl << endl;
		cout << a->visualize();
	}

	// query the user for an answer and retrieve the answer.
	string answer;
	do {
		cout << "Please specify whether the Conjecture is equivalent (y/n): ";
		cin >> answer;
		if (answer.compare("y") == 0)
			return true;
		else if (answer.compare("n") == 0)
			return false;
		else
			cout << "Wrong Input" << endl;
	} while (true);
}
  bool answer_Membership(list<int> query) {
    string answer;
    do {
      cout << "Please classify the word '";

      // print the query on screen
      list<int>::iterator it;
      for (it = query.begin(); it != query.end(); it++)
        cout << *it;
      cout << "' (0/1): ";
      cin >> answer;
      if (answer.compare("1") == 0)
        return true;
      else if (answer.compare("0") == 0)
        return false;
      else
        cout << "Wrong Input" << endl;
    } while (true);

    return answer.compare("1") == 0 ? true : false;
  }
  void expandAlphabet(){
    alphabetsize+=1;
  }
  int getAlphabetSize(){
    return alphabetsize;
  }
};
