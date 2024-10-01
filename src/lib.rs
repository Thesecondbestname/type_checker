#![allow(dead_code)]
mod graph;
mod typecheck;

pub struct Graph<T> {
    verteces: Vec<Vertex<T>>,
}
pub struct Vertex<T> {
    data: Option<T>,
}
impl<T> Default for Vertex<T> {
    fn default() -> Self {
        Self { data: None }
    }
}

#[test]
fn test_eq() {
    let mut g = graph::Graph::new();
    let node0 = g.add_node(graph::Vertex::new(0));
    let node1 = g.add_node(graph::Vertex::new(1));
    let node2 = g.add_node(graph::Vertex::new(2));
    let node2 = g.add_node(graph::Vertex::new(1));
    g.add_edge(&node0, &node1);
    g.add_edge(&node0, &node2);
    g.add_edge(&node1, &node0);
    g.add_edge(&node1, &node2);
    g.add_edge(&node2, &node0);
    g.add_edge(&node2, &node1);
    g.print_graph();
    panic!();
}
