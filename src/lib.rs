use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
struct Node {
    id: usize,
    edges: Vec<usize>, // Connected Edge IDs
}

#[derive(Debug, Clone, PartialEq)]
struct Edge {
    id: usize,
    from: usize, // Node ID
    to: usize,   // Node ID
    kind: EdgeKind,
}

#[derive(Debug, Clone, PartialEq, Copy)]
enum EdgeKind {
    Straight,
    Squiggly,
}

#[derive(Debug, Clone, PartialEq)]
struct Graph {
    nodes: HashMap<usize, Node>,
    edges: HashMap<usize, Edge>,
    next_id: usize, // Counter for unique IDs
}

// TODO: Remove nodes that have no edges
// Note that there should never be edges with no nodes. Check this.
impl Graph {
    fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            edges: HashMap::new(),
            next_id: 0,
        }
    }

    // We create dangling nodes, then join the edges later
    fn add_node(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.nodes.insert(id, Node { id, edges: vec![] });
        id
    }

    // Delete dangling nodes
    fn remove_node(&mut self, id: usize) {
        // TODO: is assert! the Rust convention here?
        assert!(
            self.nodes.get(&id).unwrap().edges.is_empty(),
            "Trying to remove a node that has edges!"
        );
        self.nodes.remove(&id);
    }

    // To create an edge we need two nodes
    fn add_edge(&mut self, from: usize, to: usize, kind: EdgeKind) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.edges.insert(id, Edge { id, from, to, kind });
        // Update the edges of the FROM and TO nodes.
        if let Some(node1) = self.nodes.get_mut(&from) {
            node1.edges.push(id);
        }
        if let Some(node2) = self.nodes.get_mut(&to) {
            node2.edges.push(id);
        }
        id
    }

    fn remove_edge(&mut self, id: usize) {
        let edge = self.edges.get_mut(&id).unwrap();
        // Update the nodes
        if let Some(from) = self.nodes.get_mut(&edge.from) {
            from.edges.retain(|&x| x != id);
        }
        if let Some(to) = self.nodes.get_mut(&edge.to) {
            to.edges.retain(|&x| x != id);
        }
        // Update the Graph
        self.edges.remove(&id);
    }

    // If a vertex has no edges, then remove it
    // If a vertex connects only 2 edges, then remove it and rejoin
    fn consolidate_node(&mut self, id: usize) {
        // Get the edges connected to the node
        let node = self.nodes.get(&id).expect("Node not found!");
        let edges = &node.edges;

        // Only consolidate if the node has exactly 2 edges
        if edges.len() != 2 {
            return;
        }

        // Collect the edges and the nodes they connect to
        // Note: this copies the usize values, so we drop the reference to self
        // which means we're able to mutate it later
        let edge1_id = edges[0];
        let edge2_id = edges[1];

        // If we have no edges at all then remove the node
        if edges.len() == 0 {
            eprintln!("Warning: Found a node with no edges!");
            self.remove_node(id);
        }

        // Get the connected nodes
        let edge1 = self.edges.get(&edge1_id).expect("Edge not found!");
        let edge2 = self.edges.get(&edge2_id).expect("Edge not found!");
        let node1 = other_node(edge1, id);
        let node2 = other_node(edge2, id);

        // Create a new edge connecting node1 and node2
        self.add_edge(node1, node2, edge1.kind);

        // Remove the old edges
        self.remove_edge(edge1_id);
        self.remove_edge(edge2_id);

        // Remove the intermediate node
        self.remove_node(id);
    }
}

fn other_node(edge: &Edge, id: usize) -> usize {
    if edge.from == id {
        edge.to
    } else {
        edge.from
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_remove_edge() {
        let mut graph = Graph::new();
        let node1 = graph.add_node();
        let node2 = graph.add_node();
        let edge = graph.add_edge(node1, node2, EdgeKind::Straight);
        println!("Before: {:#?}", graph);
        graph.remove_edge(edge);
        println!("After: {:#?}", graph);
        assert_eq!(graph.edges.len(), 0);
        for node in graph.nodes.values() {
            assert_eq!(node.edges.len(), 0);
        }
    }

    #[test]
    fn test_clone_graph() {
        let mut graph = Graph::new();
        let node1 = graph.add_node();
        let node2 = graph.add_node();
        graph.add_edge(node1, node2, EdgeKind::Straight);
        let cloned = graph.clone();
        println!("Original: {:#?}", graph);
        println!("Cloned: {:#?}", cloned);
        assert_eq!(graph, cloned);
    }

    #[test]
    fn test_consolidate_node() {
        let mut graph = Graph::new();
        let node1 = graph.add_node();
        let node2 = graph.add_node();
        let node3 = graph.add_node();
        graph.add_edge(node1, node2, EdgeKind::Straight);
        graph.add_edge(node2, node3, EdgeKind::Straight);
        println!("Before: {:#?}", graph);
        graph.consolidate_node(node2);
        println!("After: {:#?}", graph);
        assert!(graph.nodes.len() == 2);
        assert!(graph.edges.len() == 1);
    }
}
