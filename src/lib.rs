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


// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn it_works() {
//         let result = add(2, 2);
//         assert_eq!(result, 4);
//     }
// }
