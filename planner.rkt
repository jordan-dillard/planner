#lang dssl2

# HW7: Trip Planner
#
# ** You must work on your own for this assignment. **

let eight_principles = ["Know your rights.", "Acknowledge your sources.",
"Protect your work.",
"Avoid suspicion.",
"Do your own work.",
"Never falsify a record or permit another person to do so.",
"Never fabricate data, citations, or experimental results.",
"Always tell the truth when discussing your work with your instructor."]


# Your program will most likely need a number of data structures, many of
# which you've implemented in previous homeworks.
# We have provided you with compiled versions of homework 3, 4, 5, and 6
# solutions. You can import them as you did in homework 6.
# Be sure to extract the `hw7-lib` archive is the same directory as this file.
# You may also import libraries from the DSSL2 standard library (e.g., cons,
# array, etc.).

import cons
import 'hw7-lib/graph.rkt'
import 'hw7-lib/hashtable.rkt'
import 'hw7-lib/binheap.rkt'
import 'hw7-lib/unionfind.rkt'
import sbox_hash
import array

### Basic Vocabulary Types ###

#  - Latitudes and longitudes are numbers:
let Lat?  = num?
let Lon?  = num?
#  - Point-of-interest categories and names are strings:
let Cat?  = str?
let Name? = str?

# ListC[T] is a list of `T`s (linear time):
let ListC = Cons.ListC

# List of unspecified element type (constant time):
let List? = Cons.list?


### Input Types ###

#  - a SegmentVector  is VecC[SegmentRecord]
#  - a PointVector    is VecC[PointRecord]
# where
#  - a SegmentRecord  is [Lat?, Lon?, Lat?, Lon?]
#  - a PointRecord    is [Lat?, Lon?, Cat?, Name?]


### Output Types ###

#  - a NearbyList     is ListC[PointRecord]; i.e., one of:
#                       - None
#                       - cons(PointRecord, NearbyList)
#  - a PositionList   is ListC[Position]; i.e., one of:
#                       - None
#                       - cons(Position, PositionList)
# where
#  - a PointRecord    is [Lat?, Lon?, Cat?, Name?]  (as above)
#  - a Position       is [Lat?, Lon?]

# STRUCTS   
struct Pos:
    let lat
    let lon
    
struct Seg:
    let start
    let end
    
struct POI:
    let pos
    let cat
    let name

struct Dist_Pred:
    let dist
    let pred
    
struct Dist_POI:
    let dist
    let poi

# Interface for trip routing and searching:
interface TRIP_PLANNER:
    # Finds no more than `n` points-of-interest of the given category
    # nearest to the source position. (Ties for nearest are broken
    # arbitrarily.)
    def find_nearby(
            self,
            src_lat:  Lat?,     # starting latitude
            src_lon:  Lon?,     # starting longitude
            dst_cat:  Cat?,     # point-of-interest category
            n:        nat?      # maximum number of results
        )   ->        List?     # list of nearby POIs (NearbyList)

    # Finds the shortest route, if any, from the given source position
    # (latitude and longitude) to the point-of-interest with the given
    # name. (Returns `None` if no path can be found.)
    def find_route(
            self,
            src_lat:  Lat?,     # starting latitude
            src_lon:  Lon?,     # starting longitude
            dst_name: Name?     # name of goal
        )   ->        List?     # path to goal (PositionList)
        
    # HELPERS
        
    def get_all_pos(self, segs: vec?, pois: vec?) -> Array?
    
    def seg_weight(self, pos_1: Pos?, pos_2: Pos?) -> nat?
    
    def dijkstra_search(self, graph: WuGraph?, start: Pos?) -> Array?
    

        
class TripPlanner[X] (TRIP_PLANNER): 
    let _pos_poi_hash
    let _name_poi_hash
    
    let _i_pos_hash
    let _pos_i_hash
    
    let _pos_graph
    let _positions
    let _all_pois
    
    # constructor
    def __init__(self, segs: vec?, pois: vec?):
        self._pos_poi_hash = HashTable(pois.len(), SboxHash64().hash)
        self._name_poi_hash = HashTable(pois.len(), SboxHash64().hash)
        self._all_pois = Array(0)
        for element in pois:
            
            let value = POI(Pos(element[0], element[1]), element[2], element[3])
            self._all_pois.push(value)
            let key = value.pos
            self._pos_poi_hash[key] = value
            
            key = value.name
            self._name_poi_hash[key] = value   
        self._positions = self.get_all_pos(segs, pois)
        self._i_pos_hash = HashTable(pois.len(), SboxHash64().hash)
        self._pos_i_hash = HashTable(pois.len(), SboxHash64().hash)
        for i in range(self._positions.len()):
            let value = self._positions.get(i)
            let key = i
            # if pois is empty, the i-pos hash table cannot hash a key of 0
            if pois.len() != 0:
                self._i_pos_hash[key] = value
            ## ^ this is the line...?
            value = i
            # if pois is empty, the i-pos hash table cannot hash a key of 0
            key = self._positions.get(i)
            if pois.len() != 0:
                self._pos_i_hash[key] = value   
        self._pos_graph = WuGraph(self._positions.len())    
        for element in segs:
            let pos_1 = Pos(element[0], element[1])
            let pos_2 = Pos(element[2], element[3])
            if pois.len() != 0:
                let index_1 = self._pos_i_hash[pos_1]
                let index_2 = self._pos_i_hash[pos_2]
                self._pos_graph.set_edge(index_1, index_2, self.seg_weight(pos_1, pos_2))
        
#### HELPERS ####
    def seg_weight(self, pos_1: Pos?, pos_2: Pos?):
        return ((pos_1.lon - pos_2.lon)**2 + (pos_1.lat - pos_2.lat)**2)**0.5
        
    # getting every point from the segments vector
    def get_all_pos(self, segs: vec?, pois: vec?):
        let all_pos = Array(0)

        # extract points from seg list
        for seg in segs:
            for i in range(1):
                let point = Pos(seg[i], seg[i+1])
                let absent = True
                for pos in all_pos:
                    if point == pos:
                        absent = False
                if absent:
                    all_pos.push(point)
        
        # extract points from poi list
        for poi in pois:
            let absent = True
            let point = Pos(poi[0], poi[1])
            for pos in all_pos:
                if point == pos:
                    absent = False
            if absent:
                all_pos.push(point)
        
        return all_pos
    
    # converting a cons list to an array
    def cons_to_array(self, cons: List?):
        let a = Array(0)
        while cons?(cons):
            a.push(cons.car)
            cons = cons.cdr
        return a
    
    # converting an array to a vector
    def array_to_vec(self, a: Array?):
        return [a.get(i) for i in range(a.len())]
    
    # converting a vector to a cons list    
    def vec_to_cons(self, v: vec?):
        let c = cons(None, None)
        for i in range(v.len()):
            if i == 0:
                c.car = v[i]
            elif i == 1:
                c.cdr = cons(v[i], None)
            else:
                let current = c
                while cons?(current.cdr):
                    current = current.cdr
                current.cdr = cons(v[i], None)
        
        return c
         
    def dijkstra_search(self, graph: WuGraph?, start: Pos?):
         
         let dist = [inf for i in range(self._positions.len())]
         let pred = [None for i in range(self._positions.len())]
         
         let start_i = self._pos_i_hash[start]
         dist[start_i] = 0
         let done = Array(0)
         let todo = BinHeap(graph.len()**2, λ x, y: dist[x] < dist[y]) ## FIX THE LAMBDA
         todo.insert(start_i)
         
         while todo.len() > 0:
             
             let v = todo.find_min()
             todo.remove_min()
             
             let v_is_absent = True
             for vertex in done:
                 if v == vertex:
                     v_is_absent = False
             if (v_is_absent) & (not v == None):
              
                 done.push(v)
                 let adjacents_cons = graph.get_adjacent(v)
                 let adjacents = self.cons_to_array(adjacents_cons)
                 
                 for u in adjacents:
                     let v_dist = dist[v]
                     let weight = graph.get_edge(u,v)
                     let u_dist = dist[u]
                     
                     if v_dist + weight < u_dist:
                        dist[u] = dist[v] + weight
                        pred[u] = v 
                        todo.insert(u)
         
         let dist_preds = Array(0)
         for i in range(self._positions.len()):
             dist_preds.push(Dist_Pred(dist[i], pred[i]))
         
         return dist_preds
         
    # converting a vector of POIs to a vector of vectors
    def pois_struct_to_values(self, v: vec?):
        for i in range(v.len()):
            let poi = v[i]
            v[i] = [poi.pos.lat, poi.pos.lon, poi.cat, poi.name]
            
        return v
            
    # converting a vector of positions to a vector of vectors
    def pos_struct_to_values(self, a: Array?):
        for i in range(a.len()):
            let pos = a.get(i)
            a.set(i, [pos.lat, pos.lon])
            
        return a
        
    #
    def valid_pos?(self, p: Pos?, a: Array?):
        let is_valid = False
        for pos in a:
            if p == pos:
                is_valid = True
        
        return is_valid
         
# for every vertex v in graph do
#	Dist[v] ← infinity;
#	Pred[v] ← none
#End
#Dist[start] ← 0;
#
#todo ← the set of vertices in graph;
#While todo is not empty do
#	V ← remove the element of todo with minimal dist[v];
#	For every outgoing edge (v, u) with weight w in graph do:
#		If dist[v] + w < dist[u] then
#			Dist[u] ← dist[u] + w;
#			Pred[u] ← v
#		End
#	End
#End
            
### QUERIES ###  
    # query 1  
    def find_nearby(self, src_lat: Lat?, src_lon: Lon?, dst_cat: Cat?, n: nat?):
        # 0. ... if there are no POIs:
        if self._pos_poi_hash.len() == 0:
            return None
        
        # 1. lat, lon -> start pos
        let start_pos = Pos(src_lat, src_lon)
        
            # checks if the start_pos is valid
        
        if not self.valid_pos?(start_pos, self._positions):
            error('The position associated with the starting latitude and longitude is not valid')
        
        # 2. dijkstra's algorithm (pos graph, start pos)
            # requires: GRAPH of positions, FUNCTION (dijkstra)
        # 3. store list of end points and their distances
            # requires: STRUCT of positions and nats
        let dist_preds = self.dijkstra_search(self._pos_graph, start_pos)
        
        # 4. filter list for end points associated with POIs
            # requires: HASH TABLE of [key: pos, value: POI]
        
        let nearby = Array(0)
        for i in range(self._positions.len()):
            let pos = self._i_pos_hash[i]
            if self._pos_poi_hash.mem?(pos):
                let dist = dist_preds.get(i).dist
                #account for multiple POIs at one position???
                for poi in self._all_pois:
                    if (poi.pos == pos) & (poi.cat == dst_cat):
                        let dist_poi = Dist_POI(dist, poi)
                        nearby.push(dist_poi)
        nearby = self.array_to_vec(nearby)
        
        # 5. order list from nearest to furthest
        heap_sort(nearby, λ x, y: x.dist < y.dist)
        # 6. return a list of the first n elements from this list
        if n > nearby.len():
            n = nearby.len()
        nearby = [nearby[i].poi for i in range(n)]
        nearby = self.pois_struct_to_values(nearby)
        nearby = self.vec_to_cons(nearby)
        
        #if, in this cons list of POIs nearby poi_1, the first POI in the list IS poi_1, remove it
        if self._pos_poi_hash.mem?(start_pos):
            if nearby.car == self._pos_poi_hash[start_pos]:
                nearby = nearby.cdr
    
        if nearby.car == None:
            nearby = None
                
        return nearby
        
    # query 2
    def find_route(self, src_lat: Lat?, src_lon: Lon?, dst_name: Name?):
         # 0. ... if there are no POIs:
        if self._pos_poi_hash.len() == 0:
            return None
        
        # 1. lat, lon -> start pos
        let start_pos = Pos(src_lat, src_lon)
        
             # checks if the start_pos is valid
        if not self.valid_pos?(start_pos, self._positions):
            error('The position associated with the starting latitude and longitude is not valid')
        
        # 2. dijkstra's algorithm (pos graph, start pos)
            # requires: GRAPH of positions
        let dist_preds = self.dijkstra_search(self._pos_graph, start_pos)
        # 3. name -> POI
            # requires: HASH TABLE of [key: name, value: POI]
        if not self._name_poi_hash.mem?(dst_name):
            return None
        let dst_poi = self._name_poi_hash[dst_name]
        # 4. POI -> pos
            # access pos from POI struct
        let dst_pos = dst_poi.pos
        # 5. pos -> index
            # search within function
        let start_i = 0
        let end_i = 0
        for i in range(self._positions.len()):
            if self._positions.get(i) == start_pos:
                start_i = i
            if self._positions.get(i) == dst_pos:
                end_i = i
        # 6. go from pred[end pos] -> start pos, adding each step to a list
        let path = Array(0)
        let current_i = end_i
        while (not current_i == start_i) & (current_i != None):
            path.push(self._positions.get(current_i))
            current_i = dist_preds.get(current_i).pred
        if current_i != None:
            path.push(self._positions.get(current_i))
        # 7. re-order list and return it
        for i in range(path.len()/2):
            let temp = path.get(i)
            path.set(i, path.get(path.len()-1-i))
            path.set(path.len()-1-i, temp)
        
        path = self.pos_struct_to_values(path)
        path = self.vec_to_cons(self.array_to_vec(path))
        
        # if there is no path to the destination from the starting position...
        if (path.cdr == None) & (path.car != [src_lat, src_lon]):
            path = None
        
        return path

test 'find_nearby':
    let roads = [[0,0,1,0], [0,1,1,1],[0,2,1,2],[0,0,0,1],[1,0,1,1],[0,1,0,2],[1,1,1,2],[1,2,1,3],[1,3,-0.2,3.3]]
    let pois = [[0,0, 'food', 'Sandwiches'], [0,1, 'food', 'Pasta'], [1,1, 'bank', 'Local Credit Union'], [1,3, 'bar', 'Bar None'], [1, 3, 'bar', 'H Bar'], [-0.2, 3.3, 'food', 'Burritos']]
    let tp = TripPlanner(roads, pois)
    
    assert tp.find_nearby(0, 2, "food", 3) == cons([0,1 , "food", "Pasta"], cons([0,0, "food", "Sandwiches"], cons([-0.2,3.3, "food", "Burritos"], None)))
    
test 'find_routes':
    let roads = [[0,0,1,0], [0,1,1,1],[0,2,1,2],[0,0,0,1],[1,0,1,1],[0,1,0,2],[1,1,1,2],[1,2,1,3],[1,3,-0.2,3.3]]
    let pois = [[0,0, 'food', 'Sandwiches'], [0,1, 'food', 'Pasta'], [1,1, 'bank', 'Local Credit Union'], [1,3, 'bar', 'Bar None'], [1, 3, 'bar', 'H Bar'], [-0.2, 3.3, 'food', 'Burritos']]
    let tp = TripPlanner(roads, pois)
    
    assert tp.find_route(0, 0, "Burritos") == cons([0,0], cons([1,0], cons([1,1], cons([1,2], cons([1,3], cons([-0.2,3.3], None))))))
    
test 'unconnected POIs':
    let roads = [[0,0,1,0], [1,0,1,1],[1,1,0,-1],[0,-1,0,0]]
    let pois = [[0,0, 'food', 'Sandwiches'], [1,1, 'food', 'Pasta'], [0.7,0.7, 'bank', 'Local Credit Union']]
    let tp = TripPlanner(roads, pois)
    
    assert tp.find_route(0, 0, "Pasta") == cons([0,0], cons([1,0], cons([1,1], None)))
    assert tp.find_route(0.7, 0.7, "Pasta") == None
    
test 'ghost town: no POIs, aka Wisconsin (no tea no shade Wisconsin)':
    let roads = [[0,0,1,0], [1,0,1,1],[1,1,0,-1],[0,-1,0,0]]
    let pois = []
    let tp = TripPlanner(roads, pois)
    
    assert tp.find_nearby(0,0, "food", 3) == None
    assert tp.find_route(0,0, "Pasta") == None
    
test 'multiple POIs at the same pos':
    let roads = [[0,0,1,0], [0,1,1,1],[0,2,1,2],[0,0,0,1],[1,0,1,1],[0,1,0,2],[1,1,1,2],[1,2,1,3],[1,3,-0.2,3.3]]
    let pois = [[0,0, 'food', 'Sandwiches'], [0,1, 'food', 'Pasta'], [1,1, 'bank', 'Local Credit Union'], [1,3, 'bar', 'Bar None'], [1, 3, 'bar', 'H Bar'], [-0.2, 3.3, 'food', 'Burritos']]
    let tp = TripPlanner(roads, pois)
    
    assert tp.find_nearby(0,2,"bar", 1) == cons([1, 3, "bar", "Bar None"], None)
    assert tp.find_nearby(0,2,"bar", 2) == cons([1, 3, "bar", "Bar None"], cons ([1, 3, "bar", "H Bar"], None))
    
    
test 'find_route to POI that doesn''t exist':
    let roads = [[0,0,1,0], [0,1,1,1],[0,2,1,2],[0,0,0,1],[1,0,1,1],[0,1,0,2],[1,1,1,2],[1,2,1,3],[1,3,-0.2,3.3]]
    let pois = [[0,0, 'food', 'Sandwiches'], [0,1, 'food', 'Pasta'], [1,1, 'bank', 'Local Credit Union'], [1,3, 'bar', 'Bar None'], [1, 3, 'bar', 'H Bar'], [-0.2, 3.3, 'food', 'Burritos']]
    let tp = TripPlanner(roads, pois)
    
    assert tp.find_route(1,2, "Sushi") == None
    
test 'find_route with closer and closer starting position':
    let roads = [[0,0,1,0], [0,1,1,1],[0,2,1,2],[0,0,0,1],[1,0,1,1],[0,1,0,2],[1,1,1,2],[1,2,1,3],[1,3,-0.2,3.3]]
    let pois = [[0,0, 'food', 'Sandwiches'], [0,1, 'food', 'Pasta'], [1,1, 'bank', 'Local Credit Union'], [1,3, 'bar', 'Bar None'], [1, 3, 'bar', 'H Bar'], [-0.2, 3.3, 'food', 'Burritos']]
    let tp = TripPlanner(roads, pois)
    
    assert tp.find_route(1,2,"Burritos") == cons([1,2], cons([1,3], cons([-0.2, 3.3], None)))
    assert tp.find_route(1,3,"Burritos") == cons([1,3], cons([-0.2,3.3], None))
    assert tp.find_route(-0.2,3.3, "Burritos") == cons([-0.2,3.3], None)
    
test 'find_nearby POIs of same category from slightly different POIs':
    let roads = [[0,0,1,0], [0,1,1,1],[0,2,1,2],[0,0,0,1],[1,0,1,1],[0,1,0,2],[1,1,1,2],[1,2,1,3],[1,3,-0.2,3.3]]
    let pois = [[0,0, 'food', 'Sandwiches'], [0,1, 'food', 'Pasta'], [1,1, 'bank', 'Local Credit Union'], [1,3, 'bar', 'Bar None'], [1, 3, 'bar', 'H Bar'], [-0.2, 3.3, 'food', 'Burritos']]
    let tp = TripPlanner(roads, pois)
    
    assert tp.find_nearby(1,3,"food",1) == cons([-0.2,3.3,"food","Burritos"], None)
    assert tp.find_nearby(0,2,"food",1) == cons([0,1,"food", "Pasta"], None)
    assert tp.find_nearby(0, 1, "food", 2) == cons([0, 1, "food", "Pasta"], cons ([0, 0, "food", "Sandwiches"], None))
    
test 'invalid starting positions input':
    let roads = [[0,0,1,0], [0,1,1,1],[0,2,1,2],[0,0,0,1],[1,0,1,1],[0,1,0,2],[1,1,1,2],[1,2,1,3],[1,3,-0.2,3.3]]
    let pois = [[0,0, 'food', 'Sandwiches'], [0,1, 'food', 'Pasta'], [1,1, 'bank', 'Local Credit Union'], [1,3, 'bar', 'Bar None'], [1, 3, 'bar', 'H Bar'], [-0.2, 3.3, 'food', 'Burritos']]
    let tp = TripPlanner(roads, pois)
    
    assert_error tp.find_nearby(0.1,0.2,"food",1)
    assert_error tp.find_route(10, 20,"Sandwiches")