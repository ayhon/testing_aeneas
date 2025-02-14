#![feature(box_patterns)]

// use std::cmp::{min,max};
fn max(a: i8, b: i8) -> i8 {
    if a > b { a } else { b }
}
fn min(a: i8, b: i8) -> i8 {
    if a < b { a } else { b }
}

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


impl<T> BinTree<T> {
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

    fn contains(&self, target: &T) -> bool 
    where T: Eq
    {
        
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
            Self::Node{left, right, ..} => {
                left.reverse();
                right.reverse();
                std::mem::swap(left, right)
            }
        }
    }
}


enum BSTree<T> {
    Nil,
    Node {
        value: T,
        left: Box<BSTree<T>>,
        right: Box<BSTree<T>>,
    }
}

impl BSTree<isize>{
    fn contains(&self, target: &isize) -> bool {
        match self {
            Self::Nil => false,
            Self::Node{value: curr, left, right} =>
                if *target == *curr {
                    true
                } else if *target < *curr {
                    left.contains(target)
                } else {
                    right.contains(target)
                }
        }
    }
    fn insert(&mut self, value: isize) {
        match self {
            Self::Nil => {
                let new_node = Self::Node{
                    value,
                    left: Box::new(Self::Nil),
                    right: Box::new(Self::Nil)
                };
                std::mem::replace(self, new_node);
            }
            Self::Node{value: curr, left, right} => {
                if value < *curr {
                    left.insert(value)
                } else if *curr < value {
                    right.insert(value)
                }
            }
        }
    }
}

enum AVLTree<T> {
    Nil,
    Node {
        value: T,
        left: Box<AVLTree<T>>,
        right: Box<AVLTree<T>>,
        bf: i8,
    }
}

impl AVLTree<isize>{
    fn contains(&self, target: &isize) -> bool {
        match self {
            Self::Nil => false,
            Self::Node {value, left, right, ..} => {
                if *target == *value {
                    true
                } else if *target < *value {
                    left.contains(target)
                } else {
                    right.contains(target)
                }
            }
        }
    }


    fn rotateLeft(self) -> Self {
        match self {
            Self::Node{
                value: value_out,
                bf: bf_out, // l - max(m,r) - 1
                left,
                right: box Self::Node {
                    value: value_in,
                    bf: bf_in, // m - r
                    left: middle,
                    right,
                },
            } => {
                /* bf_4 := l - m
                * if bf_in >= 0 then bf_out + 1         
                *   (m <= r)     (l - m - 1 + 1)
                * if bf_in > 0  then bf_out - bf_in + 1 
                *   (m >  r)     (l - r - 1 - m + r + 1)
                * generally, bf_out - max(bf_in, 0)
                */
                let bf_4 = bf_out - max(bf_in, 0);
                /* bf_3 := 1 + max(l, m) - r
                * if bf_4 >= 0 then bf_3      =  1 + bf_4    + bf_in
                *  (l - m)          1 + l - r =  1 + (l - m) + (m - r)
                * if bf_4 <  0 then 1 + m - r
                *  (l - m)          1 + bf_in
                * generally 1 + bf_in + max(bf_4, 0)
                */
                let bf_3 = 1 + bf_in + max(bf_4, 0);
                Self::Node {
                    value: value_in,
                    bf: bf_3,                     
                    left: Box::new(Self::Node {
                        value: value_out,
                        bf: bf_4, 
                        left,
                        right: middle
                    }),
                    right,
                }
            }
            _ => self,
        }
    }

    fn rotateRight(self) -> Self {
        match self {
            Self::Node{
                value: value_out,
                bf: bf_out, // 1 + max(l, m) - r
                left: box Self::Node {
                        value: value_in,
                        bf: bf_in, // l - m
                        left,
                        right: middle,
                    },
                right
            }=> {
                // bf_4 = m - r
                // if bf_in > 0 then bf_out     - bf_in   - 1
                //   (l > m)        (1 + l - r) - (l - m) - 1
                // if bf_in < 0 then bf_out     - 1
                //   (l < m)        (1 + m - r) - 1
                // generally, bf_out - min(bf_in, 0) - 1
                let bf_4 = bf_out - min(bf_in, 0) - 1;
                // bf_3 = l - max(m, r) - 1
                // if bf_4 > 0 then bf_in - 1
                //   (m > r)      (l - m) - 1
                // if bf_4 < 0 then bf_in + bf_4    - 1
                //   (m < r)      (l - m) + (m - r) - 1
                // generally, bf_in + min(bf_4, 0) - 1
                let bf_3 = bf_in + min(bf_4, 0) - 1;
                Self::Node {
                    value: value_in,
                    bf: bf_3, // left.height - max(middle.height, right.height)
                    left,
                    right: Box::new(Self::Node {
                        value: value_out,
                        bf: bf_4,  // middle.height - right.height
                        left: middle,
                        right,
                    }),
                }
            }
            _ => self,
        }
    }

    fn balance_factor(&self) -> i8 {
        match self {
            Self::Nil => 0,
            Self::Node{bf, ..} => *bf,
        }
    }

    fn rebalance(self) -> Self {
        /* TODO: Ask Nadrieril about this ↓ */

        // match self {
        //     node@Self::Node { bf, ref left, .. }  // LEFT-LEFT
        //     if bf == 2 && left.balance_factor() == 1  => {
        //         node.rotateRight()
        //     }
        //     Self::Node { bf, left, right, value }  // LEFT-RIGHT
        //     if bf == 2 && left.balance_factor() == -1  => {
        //         Self::Node {
        //             value,
        //             bf,
        //             left: Box::new(left.rotateLeft()),
        //             right,
        //         }.rotateRight()
        //     }
        //     Self::Node { bf, right, left, value }  // RIGHT-LEFT
        //     if bf == -2 && right.balance_factor() == 1  => {
        //         Self::Node {
        //             value,
        //             bf,
        //             left: Box::new(left.rotateRight()),
        //             right,
        //         }.rotateLeft()
        //     }
        //     node@Self::Node { bf, ref right, .. }  // RIGHT-RIGHT
        //     if bf == -2 && right.balance_factor() == -1  => {
        //         node.rotateLeft()
        //     }
        //     _ => self
        // }
        match self {
            // TODO: Think about this a bit more
            Self::Node {
                value,
                bf: balance_factor,
                left,
                right,
            } => {
                if balance_factor == 2 { // LEFT-
                    if left.balance_factor() == 1 { // -LEFT
                        return Self::Node {
                            value,
                            bf: 2,
                            left,
                            right,
                        }.rotateRight()
                    } else if left.balance_factor() == -1 { // -RIGHT
                        return Self::Node {
                            value,
                            bf: 2,
                            left: Box::new(left.rotateLeft()),
                            right,
                        }.rotateRight()
                    }
                } else if balance_factor == -2 { // RIGHT-
                    if right.balance_factor() == -1 { // -RIGHT
                        return Self::Node {
                            value,
                            bf: -2,
                            left, 
                            right,
                        }.rotateLeft()
                    } else if right.balance_factor() == 1 { // -LEFT
                        return Self::Node {
                            value,
                            bf: -2,
                            left, 
                            right: Box::new(right.rotateRight()),
                        }.rotateLeft()
                    }
                }
                return Self::Node {
                    value,
                    bf: balance_factor,
                    left,
                    right
                }
            }
            _ => self,
        }
    }

    fn insertAndWarn(self, value: isize) -> (Self,bool) {
        match self {
            Self::Nil => (Self::Node{
                value, left: Box::new(Self::Nil), right: Box::new(Self::Nil), bf: 0
            }, false),
            Self::Node{value: curr, left, right, bf} if value != curr => {
                if value < curr {
                    let (res, did_height_increase) = left.insertAndWarn(value);
                    if did_height_increase {
                        let bf = bf + 1;
                        if bf == 2 {
                            (res.rebalance(), false)
                        } else {
                            (res, true)
                        }
                    } else {
                        (res, false)
                    }
                } else {
                    let (res, did_height_increase) = right.insertAndWarn(value);
                    if did_height_increase {
                        let bf = bf - 1;
                        if bf == -2 {
                            (res.rebalance(), false)
                        } else {
                            (res, true)
                        }
                    } else {
                        (res, false)
                    }
                }
            }
            _ => (self, false)
        }
    }

    fn insert(self, value: isize) -> Self {
        self.insertAndWarn(value).0
    }

    // fn deleteAndWarn(self, value: &isize) -> (Self,bool) {
    //     todo!()
    // }
    // fn delete(self, value: &isize) -> Self {
    //     self.deleteAndWarn(value)
    // }
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
