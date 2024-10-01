use bitset::{impl_small_type, BitSet};

#[derive(PartialEq, Eq, PartialOrd)]
pub struct VertexId(usize);
// impl Drop for VertexId {
//     fn drop(&mut self) {
//         unsafe {
//             (*self.1).verteces[self.0] = Vertex::default();
//             let edges: Vertex<_> = std::mem::take(&mut (*self.1).verteces[self as &VertexId]);
//             for edge in edges.edges {
//                 (*self.1).verteces[&edge].edges.remove(self as &VertexId);
//             }
//             (*self.1).verteces[self as &VertexId]
//                 .edges
//                 .remove(self as &VertexId);
//         }
//         unsafe {
//             (*self.1).free_slots.insert(self as &VertexId);
//         }
//         println!("Succsessfully dropped index: {} :2", self.0);
//     }
// }
impl VertexId {
    const MAX: usize = usize::MAX - 1;
}
impl std::fmt::Debug for VertexId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub struct Vertex<T> {
    data: Option<T>,
    edges: BitSet<VertexId>,
}

impl<T> Default for Vertex<T> {
    fn default() -> Self {
        Self {
            data: None,
            edges: BitSet::default(),
        }
    }
}
pub struct Graph<T> {
    verteces: Vec<Vertex<T>>,
    free_slots: BitSet<VertexId>,
}
impl_small_type!(VertexId);
impl bitset::SetElem for VertexId {
    fn index(&self) -> usize {
        self.0
    }

    fn from_u32(item: u32) -> Self {
        Self(item as usize)
    }
}
impl<T: std::fmt::Debug> Graph<T> {
    pub fn print_graph(&self) {
        println!("Graph [\n free_slots {:?}", self.free_slots);
        for (i, vertex) in self.verteces.iter().enumerate() {
            println!(
                " vertex{} {{data:{:?}, {:?}}},",
                i, vertex.data, vertex.edges
            );
        }
        println!("]\n");
    }
}
// impl Graph<VertexId> {
//     pub fn add_node(&mut self, v: Vertex<VertexId>) -> VertexId {
//         if let Some(index) = self.free_slots.first() {
//             self.verteces[&index] = v;
//             self.free_slots.remove(&index);
//             index
//         } else {
//             let vertex = VertexId(self.verteces.len(), self as *mut Graph<VertexId>);
//             self.verteces.push(v);
//             vertex
//         }
//     }
// }
impl<T> Graph<T> {
    pub const fn new() -> Self {
        Self {
            verteces: vec![],
            free_slots: bitset::new_bit_set(),
        }
    }
    pub fn add_node(&mut self, v: Vertex<T>) -> VertexId {
        if let Some(index) = self.free_slots.first() {
            self.verteces[&index] = v;
            self.free_slots.remove(&index);
            index
        } else {
            let vertex = VertexId(self.verteces.len());
            self.verteces.push(v);
            vertex
        }
    }
    pub fn add_edge(&mut self, from: &VertexId, to: &VertexId) {
        assert!(
            !(from.0 <= VertexId::MAX || to.0 <= VertexId::MAX),
            "Graph is full!"
        );
        if from == to {
            debug_assert!(false, "Added an edge to itself!");
        } else {
            self.verteces[from].edges.insert(to);
            self.verteces[to].edges.insert(from);
        }
    }
    pub fn remove_node(&mut self, v: VertexId) {
        // let edges = std::mem::take(&mut self.verteces[&v]);
        // self.free_slots.insert(&v);
        // for edge in edges.edges {
        //     self.verteces[&edge].edges.remove(&v);
        // }
        // self.verteces[&v].edges.remove(&v);
    }
}
impl<T> Vertex<T> {
    pub fn new(item: T) -> Self {
        Self {
            data: Some(item),
            edges: BitSet::default(),
        }
    }
}
impl<T> std::ops::Index<&VertexId> for Vec<Vertex<T>> {
    type Output = Vertex<T>;

    fn index(&self, index: &VertexId) -> &Self::Output {
        &self[index.0]
    }
}
impl<T> std::ops::Index<&VertexId> for [Vertex<T>] {
    type Output = Vertex<T>;

    fn index(&self, index: &VertexId) -> &Self::Output {
        &self[index.0]
    }
}
impl<T> std::ops::IndexMut<&VertexId> for [Vertex<T>] {
    fn index_mut(&mut self, index: &VertexId) -> &mut Self::Output {
        &mut self[index.0]
    }
}
impl<T> std::ops::IndexMut<&VertexId> for Vec<Vertex<T>> {
    fn index_mut(&mut self, index: &VertexId) -> &mut Self::Output {
        &mut self[index.0]
    }
}
