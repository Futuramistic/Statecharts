#include <iostream>
#include <string>
#include <list>
#include <libalf/alf.h>
#include <libalf/algorithm_angluin.h>
#include <libalf/conjecture.h>
#include </home/matek/Desktop/H/learner.cpp>

using namespace std;
using namespace libalf;

int getAlphabetSize() {
	int i;
	cout << "Please insert the alphabet size (between 1 and 10): ";
	cin >> i;
	return i;
}

bool getExpanding(Learner* learner) {
  string answer;
  int node;
  cout << "Do you want to expand any node? (y/n): ";
  cin >> answer;
  if (answer.compare("y") == 0){
    do
    {
      cout << "Which node do you want to expand? ";
      cin >> node;
      if(learner->checkIfNodeIsExpandable(node)){
        learner->expand(node);
        return true;
      }
      else{
        cout << "Wrong input!" <<endl;
      }
    }
    while(true);
  }
  else{
    return false;
  }
}

/*
 * The main method
 */
int main(int argc, char**argv) {
  int alphabetsize;
	alphabetsize = getAlphabetSize();
  Learner* learner = new Learner(alphabetsize);
  learner->learn();
	learner->display();
  while(getExpanding(learner)){learner->display();};
  delete learner;
  return 0;
}
