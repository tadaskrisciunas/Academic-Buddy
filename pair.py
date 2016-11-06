#!/usr/bin/python
# -*- coding: utf-8 -*-

import argparse
import csv
import pprint
import itertools
import re
from graph_tool.all import *
from collections import namedtuple, Counter
from collections import defaultdict

class Pairings:
  # Data format of mentee entry
  Mentee = namedtuple('Mentee', 'name, mentors, email')
  
  # Parsed csv data
  rawdata = []
  
  # Graph itself
  g = Graph()
  g, source, sink, names, cap, costs = [], [], [], [], [], []
  personVertices = []

  # Weights:
  sourceToPerson = 1
  mentorToSink = 2                # Maximal number of students which can be assigned to a mentor
  menotorCosts = [1, 10, 15, 5]   # Default penalties for choosing a mentor which n-th choice of a student. Can be initialised by method 'weights'
  
  def weights(self, w):
    """Initialise penalties for mentors. w is a list containing penalties for choosing a mentor which was first, second, third, ... choice of a student"""
    self.menotorCosts = w
  
  def __init__(self, rawcsvdata):
    """Initialise data submited"""
    self.rawdata = self.formatData(rawcsvdata)
  
  def formatData(self, rawdata):
    """Format data given such that rawdata contains a list of named tuples which includes names and chosen mentors (also emails)"""
    menteesData = []
    for mentee in rawdata:
      men = [m for m in mentee[1:-1] if m != '' and m != '-']      # Filter out blank choices
      menteesData.append( self.Mentee(name = mentee[0], mentors = men, email = mentee[-1:]) )
    return menteesData
  
  def uniqueMentors(self):
    """Return a list of all unique mentors chosen by students. Currently they are identified by names which might introduce potential bugs (if some mentors have same names or their names are mistyped)"""
    mentors = [student.mentors for student in self.rawdata ]
    mentors = list(set(itertools.chain.from_iterable(mentors)))
    return mentors
  
  def createGraph(self, mentorToChildren = {}):
    """Creates a graph suitable for maximal flow search.
    
    This is a directed graph which has a source connected to every participating student by zero-cost, 'sourceToPerson'-capacity egde (currently this is unit-capacity).
    Every mentor is connected to a sink by a zero-cost, 'mentorToSink'-capacity edge (variable 'mentorToSink' indicated the maximal number of students which can be assigned to a mentor).
    Every student is connected to all mentors that she/he has chosen by unit-capacity edge. Its cost is determined by 'menotorCosts' - first choice of a mentor should have a lower cost than all subsequent choices.
    
    In this manner, resulting min-cost max-flow will select an optimal pairing of student to mentors, subject to constraints and initialised weights.
    """
    
    # Initialisation of graph using graph_tool
    self.g = Graph()
    g = self.g  # Create an alias
    self.names = g.new_vertex_property("string")
    self.cap = g.new_edge_property("int")
    self.costs = g.new_edge_property("int")
    
    # Source and sink are initialised
    self.source = g.add_vertex()
    self.names[self.source] = "Source"
    self.sink = g.add_vertex()
    self.names[self.sink] = "Sink"
    
    # Get unique mentors and save the vertex for each mentor
    mentors = self.uniqueMentors()
    mentorsMap = {}
    
    # Initialise all mentor vertices
    for mentor in mentors:
      # Add a vertex, name it and save it in mapping 'mentorsMap' which is (mentor name -> vertex)
      v = g.add_vertex()
      self.names[v] = mentor
      mentorsMap[mentor] = v
      # Add an edge to sink
      e = g.add_edge(v, self.sink)
      
      # Allow mentors in mentorToChildren have not a default number of mentees
      if mentor in mentorToChildren:
        self.cap[e] = mentorToChildren[mentor]
      else:
        self.cap[e] = self.mentorToSink  
      self.costs[e] = 0
      
    
    # Initialise all mentees vertices
    for person in self.rawdata:
      # Add a vertex, name it, save it in mapping 'personVertices' which is (mentee name -> vertex)
      v = g.add_vertex()
      self.names[v] = person.name
      self.personVertices.append(v)
      # Add an edge to source
      e = g.add_edge(self.source, v)
      self.cap[e] = self.sourceToPerson
      self.costs[e] = 0
      
      # Initialise all edges to mentors
      for (mentor, weight) in zip(person.mentors, self.menotorCosts):
        e = g.add_edge(v, mentorsMap[mentor])     # Get mentor vertex by its name, add egde
        self.cap[e] = 1
        self.costs[e] = weight
    
  def boykov_kolmogorov(self):
    """ Depreciated method for finding just maximal-flow (with no regards to weights)"""
    # Find residual network by Boykov-Kolmogorov algorithm
    res = boykov_kolmogorov_max_flow(self.g, self.source, self.sink, self.cap)
    res.a = self.cap.a - res.a  # the actual flow
    
    # Output pairings
    for v in self.personVertices:
      r = [self.names[e.target()] for e in v.out_edges() if res[e] != 0]
      print self.names[v], " -> ", r[0]
    
    # Visualise the pairings
    pos = radial_tree_layout(self.g, self.source)
    graph_draw(self.g, pos = pos, edge_pen_width=prop_to_size(res, mi=0, ma=3, power=1), display_props = self.names)
    
  
  def bellman_ford(self, g, source, sink, costs):
    """Bellman-Ford search algorithm from source to sink.
    Returns success, dist, pred, where success is true iff there is a path from source to sink
    dist contains distances to vertices from source,
    pred contains parent vertices.
    
    It is used instead of Dijkstra since it must be able to handle negative edges;
    Faster implementations are possible using idea behind Johnsons algorithm (to transform edges using calculated weights),
    however, they are more difficult to code. Since speed is sufficient for small sets of mentors and mentees, it is currently not worth the effort.
    """
    # Create distance and parent lists
    dist = g.new_vertex_property("float")
    pred = g.new_vertex_property("int")
    
    # Initialise the vertices
    for v in g.vertices():
      dist[v] = float('inf')
      pred[v] = -1            # Ugly
    
    # Initialise source
    dist[source] = 0
    pred[source] = source
    
    # Bellman-Ford
    for x in range(g.num_vertices()):
      # Check if any egdes were relaxed during this iteration
      updated = False
      # Check if something is to be relaxed
      for e in g.edges():
        if dist[e.source()] + costs[e] < dist[e.target()]:
          updated = True
          dist[e.target()] = dist[e.source()] + costs[e]
          pred[e.target()] = e.source()
      # If no changes occured in this iteration, end Bellman-Ford
      if (not updated):
        break
    
    # Success iff there is a path to sink
    return (pred[sink] != -1), dist, pred
  
  def backtrack(self, g, source, sink, pred):
    """Given list of parent vertices 'pred', backtrack a path from sink to source. This is a generator yielding pairs of vertices"""
    # Starting vertex
    backtrack = sink
    
    # Return pairs of parent, current vertices
    # Ending vertice is its own parent
    while g.vertex(pred[backtrack]) != backtrack:
      prev = g.vertex(pred[backtrack])
      yield prev, backtrack
      backtrack = prev
    
  def find_mincost_maxflow(self, g, source, sink, cap, costs):
    """Find min-cost max-flow according to capacities 'cap' and costs 'costs', from 'source' to 'sink'."""
    # Include a boolean property to indicate if the edge is present in the graph
    # Since we will search for a path through vertices with non-zero capacities, other edges must be hidden
    present = g.new_edge_property("bool")
    
    # Iterate while flow can be increased
    success = True
    while success:
      # Mark only positive capacity edges as traversable
      for edge in g.edges():
        present[edge] = (cap[edge] > 0)
      
      # Hide zero and negative capacity edges, find flow, restore edges
      g.set_edge_filter(present)
      success, dist, pred = self.bellman_ford(g, source, sink, costs)   # Bellman-Ford from source to sink using lowest cost edges
      g.clear_filters()
      
      # If the path is found
      if success:
        # Backtrack the path from sink to source, find the bottleneck capacity
        maxflow = float('inf')
        for prev,curr in self.backtrack(g, source, sink, pred):
          maxflow = min(maxflow, cap[g.edge(prev,curr)])
        
        # For every edge on the path, reduce its capacity by found bottleneck capacity and increase reverse edges by that amount
        for prev,curr in self.backtrack(g, source, sink, pred):
          cap[g.edge(prev, curr)] = cap[g.edge(prev, curr)] - maxflow
          cap[g.edge(curr, prev)] = cap[g.edge(curr, prev)] + maxflow
    
    # Retrieve the actual flow, instead of decrease in capacity
    flow = self.g.new_edge_property("int")
    for e in self.g.edges():
      flow[e] = self.cap[e] - cap[e]
    # Return flow
    return flow
  
  def pairFromFlow(self, flow):
    assignments = []
    mentorToMentee = defaultdict(list)
    
    for v in self.personVertices:
      # Since each mentee vertex can receive at most one unit of flow, it is sufficient to check which mentor receive that flow unit
      r = [self.names[e.target()] for e in v.out_edges() if flow[e] != 0]
      if len(r) > 0:
        assignments.append( (self.names[v], r[0]) )
        mentorToMentee[r[0]].append(self.names[v]) 
      else:
        raise RuntimeError(self.names[v] + " neįmanoma priskirti mentoriaus!")
        
    return assignments, mentorToMentee
  
  def mincost_maxflow(self):
    """Find min-cost max-flow and get the mentee-mentors assigments"""
    
    # Capacities will be destroyed, thus are copied
    g = self.g.copy()
    cap, costs = self.cap.copy(), self.costs.copy()
    
    # Add a reverse edge for all present edges (as required by algorithm)
    for edge in self.g.edges():
      et = g.add_edge(edge.target(), edge.source())
      cap[et] = 0               # Current reverse edge capacity is 0 (indicating that flow backwards currently is impossible)
      costs[et] = -costs[edge]  # Since flow on reversed edges indicates a correction, its costs must be negative to compensate
    
    # Find the actual flow
    flow = self.find_mincost_maxflow(g, self.source, self.sink, cap, costs)
    
    # Construct mentee-mentor pairs from flows
    # ~ assignments = []
    # ~ for v in self.personVertices:
      # ~ # Since each mentee vertex can receive at most one unit of flow, it is sufficient to check which mentor receive that flow unit
      # ~ r = [self.names[e.target()] for e in v.out_edges() if flow[e] != 0]
      # ~ assignments.append( (self.names[v], r[0]) ) 
    assignments, mentorsToMentees = self.pairFromFlow(flow)
    
    # Return flow information for visualisation and pairings
    return flow, assignments, mentorsToMentees
    
  def showFlow(self, flow):
    p = self.g.new_vertex_property("bool")
    for v in self.g.vertices():
      p[v] = True
    p[self.sink] = False
    p[self.source] = False
  
    self.g.set_vertex_filter(p)
    graph_draw(self.g, edge_pen_width=prop_to_size(flow, mi=0, ma=3, power=1), display_props = self.names)
    self.g.clear_filters()
    # ~ pos = radial_tree_layout(self.g, self.source)
    # ~ graph_draw(g, output_size=(200, 200), vertex_size=10, display_props = names, edge_pen_width=1.2, bg_color=[1,1,1,1] )
  
  def printMentees(self, pairings, filename = None, priority = False):
    """Pretty print mentee - mentor pairs, in file (if 'filename' is given) or to stdout (if 'filename' = None).
    Priority is the list of numbers to be printed for each mentee - usually priority given for chosen mentor.
    """
    
    output = ""
    
    # Format priority
    if not priority:
      for (mentee, mentor) in pairings:
        output += "" + mentee + "," + mentor + ',\n'
    else:
      priority = [ menteeData.mentors.index(mentor) + 1 for (menteeData, (mentee, mentor)) in zip(self.rawdata, pairings) ]
      for ((mentee, mentor), prior) in zip(pairings, priority):
        output += "" + str(prior) + "," + mentee + "," + mentor + ',\n'
    
    if filename != None:
      with open(filename, 'w') as f:   # If filename is specified, write to file
        f.write(output)
    else:
      print output                     # Else, use stdout
      
  def printMentors(self, mentorsPairs, filename = None):
    """Pretty print mentor - mentees pairs, in file (if 'filename' is given) or to stdout (if 'filename' = None)."""
    # Initialise output
    output = ""
    
    # Add mentors without mentees
    for m in self.uniqueMentors():
      mentorsPairs[m]
    
    # Format mentor-mentee output
    for mentor, mentees in mentorsPairs.iteritems():
      output += mentor + ',' + ','.join(mentees) + "\n"
    
    if filename != None:
      with open(filename, 'w') as f:   # If filename is specified, write to file
        f.write(output)
    else:
      print output                     # Else, use stdout
      
  def printJSON(self, mentorsPairs, filename = None, emails = []):
    """Pretty print mentor - mentees pairs in JSON format, in file (if 'filename' is given) or to stdout (if 'filename' = None)."""
    # Initialise output
    output = "pairings:[\n"
    
    # Add mentors without mentees
    for m in self.uniqueMentors():
      mentorsPairs[m]
    
    # Store mapping mentor or mentee name |-> email
    nameToEmail = {}
    if emails:
      for name, email in emails:
        nameToEmail[name] = email
    
    mentorPairings = []
    # If emails are present
    if emails:
      # For each pairing
      for mentor, mentees in mentorsPairs.iteritems():
        # Check that all emails exist
        if mentor not in nameToEmail:
          raise Exception(mentor)
        assert(mentor in nameToEmail)
        for mentee in mentees:
          if mentee not in nameToEmail:
            raise Exception(mentee)
          assert(mentee in nameToEmail)
        # Convert names to emails
        mentorPairings.append( (nameToEmail[mentor], [nameToEmail[mentee] for mentee in mentees]) )
    else:
      # If no emails are present, keep names
      for mentor, mentees in mentorsPairs.iteritems():
        mentorPairings.append( (mentor, mentees) )
    
    
    lines = []
    
    # Format mentor-mentee output
    for mentor, mentees in mentorPairings:
      out = '{"mentor": "'  +   mentor + '", ' + '\n'
      out += '"secondaryMentor": "",' + '\n'
      out += '"pupils": ["' + '","'.join(mentees) + '"]}'
      lines.append(out)
      
    output += ',\n'.join(lines) + ']\n'
    
    if filename != None:
      with open(filename, 'w') as f:   # If filename is specified, write to file
        f.write(output)
    else:
      print output                     # Else, use stdout
  
  def statistics(self, pairings, mentorsPairs):

    choices = Counter() 
    priority = [ menteeData.mentors.index(mentor) + 1 for (menteeData, (mentee, mentor)) in zip(self.rawdata, pairings) ]
    for p in priority:
      choices[p] += 1
      
    # ~ print choices
    for x in range(1, 4):
      print round(100.0 * choices[x] / sum(choices.values()), 1), "% iš", x, "pasirinkimų", "(" + str(choices[x]), "mokiniai)"
      

def readmentors():
  """Read data about pupils and mentors from file"""
  
  # Initialise command line parameters
  parser = argparse.ArgumentParser(description='''Įrankis suporuoti mokiniams ir mentoriams.
  Pasirinkimai įvedami iš .csv failo, kurio stulpeliai:

  Mokinio vardas | Pirmas mentorius | Antras mentorius | Trečias mentorius | Mokinio e-paštas
  ''')
  parser.add_argument('mentorsfile', metavar='failas', type=argparse.FileType('r'), help='mokinių pasirinkimų failas')
  parser.add_argument("-e", '--emails', metavar='emailai', type=argparse.FileType('r'), help='mentorių ir mokinių e. paštų failas')

  # Get filename
  args = parser.parse_args()

  # Strip entries of leading and trailing spaces
  reader = csv.reader(args.mentorsfile)
  data = [ [entry.strip() for entry in row] for row in reader ]
  
  # Check if emails file is present:
  emails = []
  if args.emails:
    emails = [email.strip() for email in args.emails.read().split(',')]
    emails = [ re.split('[<>]', email) for email in emails ]
    emails = [ (email[0].strip(), email[1].strip() ) for email in emails ]
  
  return data, emails

data, emails = readmentors()
pairs = Pairings(data)

pairs.createGraph({"Mantas Malys" : 3, "Vytautė Boreikaitė" : 3},)
# ~ pairs.createGraph({"Mantas Malys" : 3, "Vytautė Boreikaitė" : 2},)
pairs.weights([1, 10, 15, 50])
# ~ Pairings.boykov_kolmogorov(pairs)
flow, assigments, mentorsPairs = pairs.mincost_maxflow()
pairs.printMentees(assigments, "mentees", priority = True)
pairs.printMentors(mentorsPairs, "mentors")
pairs.printJSON(mentorsPairs, "json", emails)
pairs.statistics(assigments, mentorsPairs)
pairs.showFlow(flow)

