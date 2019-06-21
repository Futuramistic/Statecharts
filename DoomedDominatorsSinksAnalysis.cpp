#include <cstddef>
#include <set>
#include <vector>
#include <libalf/conjecture.h>
#include <boost/exception/all.hpp>
#include <boost/numeric/ublas/matrix.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/dominator_tree.hpp>
#include <iostream>

using namespace boost;
using namespace boost::numeric::ublas;
using namespace libalf;
using namespace std;

namespace {
void dfs(std::vector<bool> &visited, const matrix<int> &matrix, int s, const size_t numOfVertices) {
  visited[s] = true;
  for (size_t t = 0; t < numOfVertices; ++t)
    if (!visited[t] && (matrix(s, t) >= 0))
      dfs(visited, matrix, t, numOfVertices);
}

bool hasAcceptingState(const Conjecture &conjecture) {
  return !static_cast<const finite_automaton &>(conjecture).get_final_states().empty();
}

int getAcceptingState(const Conjecture &conjecture) {
  const finite_automaton &automaton = static_cast<const finite_automaton &>(conjecture);
  const set<int> finalStates(automaton.get_final_states());
  if (finalStates.empty())
    BOOST_THROW_EXCEPTION(runtime_error("dds.no-accepting-state"));
  //if (finalStates.size() != 1)
    //BOOST_THROW_EXCEPTION(runtime_error("dds.multiple-accepting-states"));
  return *finalStates.rbegin();
}

matrix<int> toMatrix(const Conjecture &conjecture) {
  const int acceptingState = getAcceptingState(conjecture);
  const finite_automaton &automaton = static_cast<const finite_automaton &>(conjecture);
  const int numOfVertices = automaton.state_count;
  matrix<int> matrix(numOfVertices, numOfVertices, -1);
  for (const auto &stateAndTransitions : automaton.transitions)
    for (const auto &transition : stateAndTransitions.second)
      for (const auto &targetState : transition.second)
        if (stateAndTransitions.first != acceptingState)
          matrix(targetState, stateAndTransitions.first) = transition.first;
  return matrix;
}

struct myGraph_t {
  typedef pair<int, int> edge;
  int numOfVertices;
  std::vector<edge> edges;
};

myGraph_t toGraph(const Conjecture &conjecture) {
  const finite_automaton &automaton = static_cast<const finite_automaton &>(conjecture);
  myGraph_t myGraph;
  myGraph.numOfVertices = automaton.state_count;
  for (const auto &stateAndTransitions : automaton.transitions)
    for (const auto &transition : stateAndTransitions.second)
      for (const auto &targetState : transition.second)
        myGraph.edges.push_back(myGraph_t::edge(stateAndTransitions.first, targetState));
  return myGraph;
}

bool reachableExcludingEdge(std::vector<bool> &visited, const matrix<int> &matrix, const size_t numOfVertices, const int s, const int e, const int target) {
  if (s == target)
    return true;
  visited[s] = true;
  for (size_t t = 0; t < numOfVertices; ++t) {
    if (!visited[t] && (matrix(s, t) >= 0) && (matrix(s, t) != e))
      return reachableExcludingEdge(visited, matrix, numOfVertices, t, e, target);
  }
  return false;
}
}

set<int> getDominators(const Conjecture &conjecture) {
  if (!hasAcceptingState(conjecture))
    return set<int>();
  const myGraph_t myGraph(toGraph(conjecture));
  typedef adjacency_list<listS, listS, bidirectionalS, property<vertex_index_t, size_t>, no_property> G;
  G g(myGraph.edges.begin(), myGraph.edges.end(), myGraph.numOfVertices);

  typedef graph_traits<G>::vertex_descriptor Vertex;
  typedef property_map<G, vertex_index_t>::type IndexMap;
  typedef iterator_property_map<std::vector<Vertex>::iterator, IndexMap> PredMap;

  std::vector<Vertex> domTreePredVector, domTreePredVector2;
  IndexMap indexMap(get(vertex_index, g));
  graph_traits<G>::vertex_iterator uItr, uEnd;
  int j = 0;
  for (boost::tie(uItr, uEnd) = vertices(g); uItr != uEnd; ++uItr, ++j)
    put(indexMap, *uItr, j);

  // Lengauer-Tarjan dominator tree algorithm
  domTreePredVector = std::vector<Vertex>(num_vertices(g), graph_traits<G>::null_vertex());
  PredMap domTreePredMap = make_iterator_property_map(domTreePredVector.begin(), indexMap);

  const int root_idx = 0;
  Vertex root = vertex(root_idx, g);
  lengauer_tarjan_dominator_tree(g, root, domTreePredMap);

  const size_t max = numeric_limits<int>::max();
  std::vector<int> dom(myGraph.numOfVertices, max);
  for (boost::tie(uItr, uEnd) = vertices(g); uItr != uEnd; ++uItr)
    if (get(domTreePredMap, *uItr) != graph_traits<G>::null_vertex())
      dom[get(indexMap, *uItr)] = get(indexMap, get(domTreePredMap, *uItr));

  set<int> result;
  size_t current_state = getAcceptingState(conjecture);
  while (current_state < dom.size()) {
    result.insert(current_state);
    current_state = dom[current_state];
  }
  return result;
}

set<int> getSinks(const Conjecture &conjecture) {
  if (!hasAcceptingState(conjecture))
    return set<int>();
  const int numOfVertices = static_cast<const finite_automaton &>(conjecture).state_count;
  const int acceptingState = getAcceptingState(conjecture);
  const matrix<int> matrix = toMatrix(conjecture);
  set<int> sinks;
  for (int s = 0; s < numOfVertices; ++s) {
    if (s == acceptingState)
      continue;
    bool sink = true;
    for (int j = 0; j < numOfVertices; ++j)
      if (matrix(j, s) >= 0 && s != j) {
        sink = false;
        break;
      }
    if (sink)
      sinks.insert(s);
  }
  return sinks;
}

set<int> getDoomed(const Conjecture &conjecture) {
  if (!hasAcceptingState(conjecture))
    return set<int>();
  const int numOfVertices = static_cast<const finite_automaton &>(conjecture).state_count;
  std::vector<bool> visited(numOfVertices);
  const matrix<int> matrix(toMatrix(conjecture));
  const set<int> sinks(getSinks(conjecture));
  for (const int sink : sinks)
    dfs(visited, matrix, sink, numOfVertices);

  set<int> doomed;
  for (int t = 0; t < numOfVertices; ++t)
    if (!visited[t])
      doomed.insert(t);
  return doomed;
}

set<int> getDominatingEdges(const size_t alphabetSize, const Conjecture &conjecture) {
  if (!hasAcceptingState(conjecture))
    return set<int>();
  const int numOfVertices = static_cast<const finite_automaton &>(conjecture).state_count;
  const int acceptingState = getAcceptingState(conjecture);
  const matrix<int> matrix = toMatrix(conjecture);
  set<int> dominatingEdges;
  for (size_t excludedEdge = 0; excludedEdge < alphabetSize; ++excludedEdge) {
    std::vector<bool> visited(numOfVertices);
    if (!reachableExcludingEdge(visited, matrix, numOfVertices, acceptingState, excludedEdge, 0))
      dominatingEdges.insert(excludedEdge);
  }
  return dominatingEdges;
}
