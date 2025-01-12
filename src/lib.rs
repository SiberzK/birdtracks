use std::collections::HashMap;
use std::error::Error;
use std::fmt;

/// Represents a node in the graph.
#[derive(Debug, Clone, PartialEq)]
struct Node {
    id: usize,
    edges: Vec<usize>, // IDs of connected edges
}

/// Represents an edge in the graph.
///
/// Edges connect two nodes and can have different types.
#[derive(Debug, Clone, PartialEq)]
struct Edge {
    id: usize,
    from: usize,    // Source node ID
    to: usize,      // Target node ID
    kind: EdgeKind, // Type of the edge
}

/// Types of edges in the graph.
#[derive(Debug, Clone, PartialEq, Copy)]
enum EdgeKind {
    Straight,
    Squiggly,
}

/// Represents a graph containing nodes and edges.
#[derive(Debug, Clone, PartialEq)]
struct Graph {
    nodes: HashMap<usize, Node>, // Map of node IDs to nodes
    edges: HashMap<usize, Edge>, // Map of edge IDs to edges
    next_id: usize,              // Counter for generating unique IDs
}

// Implementation of Graph methods
impl Graph {
    /// Creates a new, empty graph.
    fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            edges: HashMap::new(),
            next_id: 0,
        }
    }

    /// Adds a new node to the graph and returns its unique ID.
    fn add_node(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.nodes.insert(id, Node { id, edges: vec![] });
        id
    }

    /// Removes a node from the graph.
    ///
    /// # Panics
    /// Panics if the node has any connected edges or if the node does not exist.
    fn remove_node(&mut self, id: usize) {
        assert!(
            self.nodes
                .get(&id)
                .expect("Node not found!")
                .edges
                .is_empty(),
            "Cannot remove a node that has edges!"
        );
        self.nodes.remove(&id);
    }

    /// Adds a new edge between two nodes and returns its unique ID.
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

    /// Removes an edge from the graph and updates the connected nodes.
    ///
    /// # Panics
    /// Panics if the edge does not exist.
    fn remove_edge(&mut self, id: usize) {
        // Remove the edge from graph
        let edge = self.edges.remove(&id).expect("Edge not Found!");
        // Update the nodes
        if let Some(from) = self.nodes.get_mut(&edge.from) {
            from.edges.retain(|&x| x != id);
        }
        if let Some(to) = self.nodes.get_mut(&edge.to) {
            to.edges.retain(|&x| x != id);
        }
    }

    /// Collapses a node with two edges into a single edge, removing the intermediate node.
    ///
    /// # Panics
    /// Panics if the node does not exist or has a number of edges other than two.
    fn collapse_node(&mut self, id: usize) {
        let node = self.nodes.get(&id).expect("Node not found!");
        let edges = &node.edges;

        assert!(
            edges.len() == 2,
            "Expected exactly 2 edges, found {}",
            edges.len()
        );

        // Collect the edges and the nodes they connect to
        // Note: this copies the usize values, so we drop the reference to self
        // which means we're able to mutate it later
        let edge1_id = edges[0];
        let edge2_id = edges[1];

        // Get the connected nodes
        let edge1 = self.edges.get(&edge1_id).expect("Edge not found!");
        let edge2 = self.edges.get(&edge2_id).expect("Edge not found!");
        let node1 = Self::other_node(edge1, id);
        let node2 = Self::other_node(edge2, id);

        // Create a new edge connecting node1 and node2
        self.add_edge(node1, node2, edge1.kind);

        // Remove the old edges
        self.remove_edge(edge1_id);
        self.remove_edge(edge2_id);

        // Remove the intermediate node
        self.remove_node(id);
    }

    /// Retrieves the node at the opposite end of the edge from the specified node
    fn other_node(edge: &Edge, id: usize) -> usize {
        if edge.from == id {
            edge.to
        } else {
            edge.from
        }
    }

    /// Validates the graph and returns a `ValidationResult`.
    fn validate(&self) -> ValidationResult {
        let validator = GraphValidator::new(self);
        validator.validate()
    }
}

/// Represents a validation error during graph validation.
#[derive(Debug)]
struct ValidationError {
    kind: ValidationErrorKind, // Type of validation error
    message: String,           // Error message
}

/// Types of validation errors.
#[derive(Debug)]
enum ValidationErrorKind {
    TooManyEdges,       // A node has more than 3 edges
    TwoSquigglyVertex,  // A node with 3 edges has more than 1 squiggly edge
    StraightToSquiggly, // A node with 2 edges has mixed edge types
    DanglingNode,       // A node has no edges
}

use ValidationErrorKind::*;

impl ValidationError {
    /// Creates a new `ValidationError`.
    fn new(kind: ValidationErrorKind) -> Self {
        ValidationError {
            message: match kind {
                TooManyEdges => "A node can have at most 3 edges.".to_owned(),
                TwoSquigglyVertex => "A node can have at most 1 squiggly edge.".to_owned(),
                DanglingNode => "A node must have at least one edge.".to_owned(),
                StraightToSquiggly => {
                    "A node with 2 edges must have edges of the same kind.".to_owned()
                }
            },
            kind,
        }
    }
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl Error for ValidationError {}

/// The result of validating a graph.
struct ValidationResult {
    valid: bool,                  // Indicates whether the graph is valid
    errors: Vec<ValidationError>, // List of validation errors (if any)
}

impl ValidationResult {
    /// Creates a new, valid `ValidationResult`.
    fn new() -> Self {
        Self {
            valid: true,
            errors: vec![],
        }
    }
}

/// Validator for checking the structural integrity of a graph.
struct GraphValidator<'a> {
    graph: &'a Graph, // Reference to the graph being validated
}

impl<'a> GraphValidator<'a> {
    /// Creates a new `GraphValidator`.
    fn new(graph: &'a Graph) -> Self {
        GraphValidator { graph }
    }

    /// Validates the entire graph and returns a `ValidationResult`.
    fn validate(&self) -> ValidationResult {
        let mut results = ValidationResult::new();
        for node in self.graph.nodes.values() {
            if let Err(e) = self.validate_node(node) {
                results.valid = false;
                results.errors.push(e);
            }
        }
        results
    }

    /// Validates a specific node and its connections.
    fn validate_node(&self, node: &Node) -> Result<(), ValidationError> {
        match node.edges.len() {
            0 => Err(ValidationError::new(DanglingNode)),
            1 => Ok(()),
            2 => self.is_straight_to_squiggly(node),
            3 => self.is_1_straight_2_squiggly(node),
            _ => Err(ValidationError::new(TooManyEdges)),
        }
    }

    /// Checks if a node with 2 edges has edges of the same kind.
    fn is_straight_to_squiggly(&self, node: &Node) -> Result<(), ValidationError> {
        let edges = &node.edges;
        let edge1 = self.graph.edges.get(&edges[0]);
        let edge2 = self.graph.edges.get(&edges[1]);

        match (edge1, edge2) {
            (Some(e1), Some(e2)) if e1.kind != e2.kind => {
                Err(ValidationError::new(StraightToSquiggly))
            }
            (Some(_), Some(_)) => Ok(()),
            _ => panic!(
                "Expected 2 valid edges, found edge1={:?}, edge2={:?}",
                edge1, edge2
            ),
        }
    }

    /// Checks if a node with 3 edges has at most 1 squiggly edge.
    fn is_1_straight_2_squiggly(&self, node: &Node) -> Result<(), ValidationError> {
        let edges = &node.edges;
        let edge1 = self.graph.edges.get(&edges[0]);
        let edge2 = self.graph.edges.get(&edges[1]);
        let edge3 = self.graph.edges.get(&edges[2]);

        match (edge1, edge2, edge3) {
            (Some(e1), Some(e2), Some(e3)) => {
                let squiggly_count = [e1, e2, e3]
                    .iter()
                    .filter(|&&edge| edge.kind == EdgeKind::Squiggly)
                    .count();
                if squiggly_count == 2 {
                    Err(ValidationError::new(TwoSquigglyVertex))
                } else {
                    Ok(())
                }
            }
            _ => panic!(
                "Expected 3 valid edges, found edge1={:?}, edge2={:?}",
                edge1, edge2
            ),
        }
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
    fn test_collapse_node() {
        let mut graph = Graph::new();
        let node1 = graph.add_node();
        let node2 = graph.add_node();
        let node3 = graph.add_node();
        graph.add_edge(node1, node2, EdgeKind::Straight);
        graph.add_edge(node2, node3, EdgeKind::Straight);
        println!("Before: {:#?}", graph);
        graph.collapse_node(node2);
        println!("After: {:#?}", graph);
        assert!(graph.nodes.len() == 2);
        assert!(graph.edges.len() == 1);
    }

    #[test]
    fn test_validate_straight_to_squiggly() {
        let mut graph = Graph::new();
        let node1 = graph.add_node();
        let node2 = graph.add_node();
        let node3 = graph.add_node();
        graph.add_edge(node1, node2, EdgeKind::Straight);
        graph.add_edge(node2, node3, EdgeKind::Squiggly);
        assert!(!graph.validate().valid);
    }

    #[test]
    fn test_validate_1_straight_2_squiggly() {
        let mut graph = Graph::new();
        let node1 = graph.add_node();
        let node2 = graph.add_node();
        let node3 = graph.add_node();
        let node4 = graph.add_node();
        graph.add_edge(node1, node2, EdgeKind::Straight);
        graph.add_edge(node1, node3, EdgeKind::Squiggly);
        graph.add_edge(node1, node4, EdgeKind::Squiggly);
        assert!(!graph.validate().valid);
    }
}
