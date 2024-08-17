#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct OneOrMore<T> {
    first: T,
    remain: Vec<T>,
}

impl<T> OneOrMore<T> {
    pub fn new(first: T) -> Self {
        OneOrMore {
            first,
            remain: vec![],
        }
    }

    pub fn make(first: T, remain: Vec<T>) -> Self {
        OneOrMore { first, remain }
    }

    pub fn make_option(mut v: Vec<T>) -> Option<OneOrMore<T>> {
        if v.len() > 0 {
            let first = v.remove(0);
            Some(OneOrMore { first, remain: v })
        } else {
            None
        }
    }

    pub fn push(&mut self, item: T) -> () {
        self.remain.push(item)
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index == 0 {
            return Some(&self.first);
        }
        self.remain.get(index - 1)
    }

    pub fn iter(
        &self,
    ) -> std::iter::Chain<std::iter::Once<&T>, std::slice::Iter<T>> {
        let x1 = std::iter::once(&self.first);
        x1.chain((&self.remain).into_iter())
    }
}
#[macro_export]
macro_rules! oneOrMore{
    ( $alone:expr ) => {
            OneOrMore::new($alone)
    };
    ( $first:expr , $($remain:expr),* ) => {
        OneOrMore::make($first,vec![$($remain,)+])
    };
}

impl<T> IntoIterator for OneOrMore<T> {
    type Item = T;
    type IntoIter = std::iter::Chain<std::iter::Once<T>, std::vec::IntoIter<T>>;
    fn into_iter(self) -> Self::IntoIter {
        let x1 = std::iter::once(self.first);
        x1.chain(self.remain.into_iter())
    }
}

#[cfg(test)]
mod one_or_more_tests {
    use super::*;
    #[test]
    fn test_alone_macro() {
        assert!(
            oneOrMore![1]
                == OneOrMore {
                    first: 1,
                    remain: vec![]
                }
        );
    }
    #[test]
    fn test_macro() {
        assert!(
            oneOrMore![1, 2, 3, 4]
                == OneOrMore {
                    first: 1,
                    remain: vec![2, 3, 4]
                }
        );
    }
}
