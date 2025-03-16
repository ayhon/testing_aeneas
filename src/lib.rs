#![feature(box_patterns)]
#![allow(dead_code)]

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

pub enum AVLTree<T> {
    Nil,
    Node {
        value: T,
        left: Box<AVLTree<T>>,
        right: Box<AVLTree<T>>,
        bf: i8,
    }
}

impl AVLTree<isize>{
    pub fn contains(&self, target: &isize) -> bool {
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
                * if bf_in >= 0  then bf_out + 1 
                *   (m >= r)     (l - m - 1 + 1)
                * if bf_in <  0 then bf_out - bf_in + 1  
                *   (m <  r)     (l - r - 1 - m + r + 1)
                * generally, bf_out - min(bf_in, 0) + 1
                */
                let bf_4 = bf_out - min(bf_in, 0) + 1;
                /* bf_3 := 1 + max(l, m) - r
                * if bf_4 >= 0 then bf_3      =  1 + bf_4    + bf_in
                *      (l >= m)     1 + l - r =  1 + (l - m) + (m - r)
                * if bf_4 <  0 then 1 + m - r
                *      (l <  m)     1 + bf_in
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
                // if bf_in >= 0 then bf_out     - bf_in   - 1
                //       (l >= m)    (1 + l - r) - (l - m) - 1
                // if bf_in <  0 then bf_out     - 1
                //       (l <  m)    (1 + m - r) - 1
                // generally, bf_out - max(bf_in, 0) - 1
                let bf_4 = bf_out - max(bf_in, 0) - 1;
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
        match self {
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

    fn rebalance_with_height_decrease(self) -> (Self, bool) {
        match self {
            Self::Node {
                value,
                bf: balance_factor,
                left,
                right,
            } if balance_factor == 2 => { // LEFT-
                let child_balance_factor = left.balance_factor();
                if child_balance_factor == -1 { // -RIGHT
                    let res = Self::Node {
                        value,
                        bf: 2,
                        left: Box::new(left.rotateLeft()),
                        right,
                    }.rotateRight();
                    (res, true)
                } else {
                    let res = Self::Node {
                        value,
                        bf: 2,
                        left,
                        right,
                    }.rotateRight();
                    (res, child_balance_factor == 1)
                }
            }
            Self::Node {
                value,
                bf: balance_factor,
                left,
                right,
            } if balance_factor == -2 => { // RIGHT-
                let child_balance_factor = right.balance_factor();
                if child_balance_factor == 1 { // -LEFT
                    let res = Self::Node {
                        value,
                        bf: -2,
                        left, 
                        right: Box::new(right.rotateRight()),
                    }.rotateLeft();
                    (res, true)
                } else { // -RIGHT
                    let res = Self::Node {
                        value,
                        bf: -2,
                        left, 
                        right,
                    }.rotateLeft();
                    (res, child_balance_factor == -1)
                }
            }
            _ => (self, false),
        }
    }

    fn insertAndWarn(self, target: isize) -> (Self,bool) {
        match self {
            Self::Nil => (Self::Node{
                value: target, left: Box::new(Self::Nil), right: Box::new(Self::Nil), bf: 0
            }, true),
            Self::Node{value: curr, left, right, bf} if target < curr => {
                let (left, did_left_height_increase) = left.insertAndWarn(target);
                let did_height_increase = did_left_height_increase && bf == 0;
                let bf = if did_left_height_increase {bf + 1} else { bf };
                let res = Self::Node{value: curr, left: Box::new(left), right, bf};
                if bf == 2 {
                    (res.rebalance(), false)
                } else {
                    (res, did_height_increase)
                }
            }
            Self::Node{value: curr, left, right, bf} if target > curr => {
                let (right, did_right_height_increase) = right.insertAndWarn(target);
                let did_height_increase = did_right_height_increase && bf == 0;
                let bf = if did_right_height_increase {bf - 1} else { bf };
                let res = Self::Node{value: curr, left, right: Box::new(right), bf};
                if bf == -2 {
                    (res.rebalance(), false)
                } else {
                    (res, did_height_increase)
                }
            }
            _ => (self, false)
        }
    }

    pub fn insert(self, value: isize) -> Self {
        self.insertAndWarn(value).0
    }

    fn updateLeftDeletion(
        value: isize,
        did_left_height_decrease: bool,
        old_bf: i8,
        left: Box<AVLTree<isize>>,
        right: Box<AVLTree<isize>>,
    ) -> (AVLTree<isize>,bool) {
        let bf = if did_left_height_decrease { old_bf - 1 } else { old_bf };
        let (res, rebalance_height_decrease) = Self::Node{
            value, left, right, bf
        }.rebalance_with_height_decrease();
        let did_height_decrease = did_left_height_decrease && bf == 0 || rebalance_height_decrease;
        (res, did_height_decrease)
    }
    fn updateRightDeletion(
        value: isize,
        did_right_height_decrease: bool,
        old_bf: i8,
        left: Box<AVLTree<isize>>,
        right: Box<AVLTree<isize>>,
    ) -> (AVLTree<isize>,bool) {
        let bf = if did_right_height_decrease { old_bf + 1 } else { old_bf };
        let (res, rebalance_height_decrease) = Self::Node{
            value, left, right, bf
        }.rebalance_with_height_decrease();
        let did_height_decrease = did_right_height_decrease && bf == 0 || rebalance_height_decrease;
        (res, did_height_decrease)
    }

    // popLeftmost tree = (tree', val, b) -> delete tree val = (tree', b)
    fn popLeftmost(self) -> (Self, isize, bool) {
        match self {
            Self::Nil => (Self::Nil, 0, false), // UNREACHABLE
            Self::Node{value: popped, left: box Self::Nil, right, ..} => (*right, popped, true),
            Self::Node{value, left, right, bf} => {
                let (left, popped, did_left_height_decrease) = left.popLeftmost();
                let (res, did_height_decrease) = Self::updateLeftDeletion(
                    value, did_left_height_decrease, bf, Box::new(left), right
                );
                (res, popped, did_height_decrease)
            }
        }
    }

    fn deleteAndWarn(self, target: &isize) -> (Self,bool) {
        match self {
            Self::Nil => (Self::Nil, false),
            Self::Node{value: curr, left, right, bf} if *target < curr => {
                let (left, did_left_height_decrease) = left.deleteAndWarn(target);
                Self::updateLeftDeletion(curr, did_left_height_decrease, bf, Box::new(left), right)
            }
            Self::Node{value: curr, left, right, bf} if *target > curr => {
                let (right, did_right_height_decrease) = right.deleteAndWarn(target);
                Self::updateRightDeletion(curr, did_right_height_decrease, bf, left, Box::new(right))
            }
            Self::Node{value: curr, left, right, bf} if *target == curr => {
                match (*left, *right) {
                    (Self::Nil, right     ) => (right, true),
                    (left,      Self::Nil ) => (left, true),
                    (left,      right     ) => {
                        let (right, popped, did_right_height_decrease) = right.popLeftmost(); 
                        Self::updateRightDeletion(popped, did_right_height_decrease, bf, Box::new(left), Box::new(right))
                    }
                }
            }
            _ => (self, false)
        }
    }
    pub fn delete(self, value: &isize) -> Self {
        self.deleteAndWarn(value).0
    }

    // // FOR TESTING
    // fn height(&self) -> usize {
    //     match self {
    //         Self::Nil => 0,
    //         Self::Node{left,right,..} => left.height().max(right.height()) + 1
    //     }
    // }
    // fn is_bs_bounded(&self, bot: isize, top: isize) -> bool {
    //     assert!(bot <= top, format!("Expected {bot} <= {top}"));
    //     match *self {
    //         Self::Nil => true,
    //         Self::Node{value, left, right, ..} => {
    //             let bounded = bot <= value && value <= top;
    //             bounded && left.bounded(bot, value) && right.bounded(value, top)
    //         }
    //     }
    // }
    // fn is_bs(&self) -> bool {
    //     self.is_bs_bounded(isize::min, isize::max)
    // }
    // fn is_avl(&self) -> bool {
    //     self.is_bs() &&
    //     match *self {
    //         Self::Nil => true,
    //         Self::Node{left,right,bf,..} => {
    //             let inv = (bf == left.height - right.height); 
    //             let bal = bf.abs() <= 2; 
    //             inv && bal && left.is_avl() && rigth.is_avl()
    //         }
    //     }
    // }
    // fn to_dot_inner(&self, parent: Option<isize>) -> Vec<String> {
    //     match self {
    //         Self::Nil => vec!(),
    //         Self::Node{value, left, right, ..} => {
    //             let mut res = vec!(format!("q{value} [label=\"{value}\"]"));
    //             if let Some(parent) = parent {
    //                 res.push(format!("q{parent} -> q{value}"));
    //             }
    //             res.extend(left.to_dot_inner(Some(*value)));
    //             res.extend(right.to_dot_inner(Some(*value)));
    //             res
    //         }
    //     }
    // }
    // pub fn to_dot(&self) -> String {
    //     let content = self.to_dot_inner(None).join("\n");
    //     format!("digraph {{\n{content}\n}}")
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
