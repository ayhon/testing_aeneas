enum Tree<T> {
    Leaf(T),
    Branch(Box<Tree<T>>, Box<Tree<T>>),
}

impl<T> Tree<T> {
    fn branch(left: Self, right: Self) -> Self {
        Self::Branch(
            Box::new(left),
            Box::new(right),
        )

    }

    fn rev(self) -> Self {
        match self {
            Self::Branch(left, right) => Self::branch(right.rev(), left.rev()),
            Self::Leaf(_) => self
        }
    }

    fn lenght(&self) -> usize {
        match self {
            Self::Branch(left, right) => 1 + left.lenght() + right.lenght(),
            Self::Leaf(_) => 1
        }
    }
}

enum BinTree<T> {
    Nil,
    Node {
        value: T,
        left: Box<BinTree<T>>,
        right: Box<BinTree<T>>,
    }
}


impl<T: Eq> BinTree<T> {
    fn nil() -> Box<Self> { Box::new(Self::Nil) }
    fn insert(&mut self, value: T) {
        match self {
            Self::Nil => {
                *self = Self::Node {value, left: Self::nil(), right: Self::nil()};
            }
            Self::Node{right, ..} => {
                right.insert(value);
            }
                
        }
    }
    fn size(&self) -> u32 {
        match self {
            Self::Nil => 0,
            Self::Node{left, right, ..} => 1 + left.size() + right.size(),
        }
    }

    fn contains(&self, target: &T) -> bool {
        match self {
            Self::Nil => false,
            Self::Node{value, left, right} =>
                // It's probably better to express as a boolean formula
                if *value == *target {
                    true
                } else {
                    left.contains(target) || right.contains(target)
                }
        }
    }

    fn reverse(&mut self) {
        match self {
            Self::Nil => (),
            Self::Node{left, right, value} => {
                left.reverse();
                right.reverse();
                std::mem::swap(left, right)
            }
        }
    }
}


// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn it_works() {
//         let result = add(2, 2);
//         assert_eq!(result, 4);
//     }
// }
