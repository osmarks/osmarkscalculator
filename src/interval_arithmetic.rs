use std::{fmt::Display, hash::{Hash, Hasher}, ops::{Add, Div, Mul, Sub, Neg}};
use anyhow::{Result, anyhow};

// This is not strictly right because 1.0 + 1.0 etc can return exact results and don't need to expand the interval.
// Unfortunately, I don't actually know how to fix that.

#[derive(Debug, Clone, Copy)]
pub struct Interval(pub f64, pub f64);

impl Add for Interval {
    type Output = Interval;

    fn add(self, rhs: Interval) -> Interval {
        Interval((self.0 + rhs.0).next_down(), (self.1 + rhs.1).next_up())
    }
}

impl Sub for Interval {
    type Output = Interval;

    fn sub(self, rhs: Interval) -> Interval {
        Interval((self.0 - rhs.1).next_down(), (self.0 - rhs.1).next_up())
    }
}

impl Mul for Interval {
    type Output = Interval;

    fn mul(self, rhs: Self) -> Interval {
        if self.0 >= 0.0 && rhs.0 >= 0.0 && self.1 >= 0.0 && rhs.1 >= 0.0 {
            // fast path
            Interval((self.0 * rhs.0).next_down(), (self.1 * rhs.1).next_up())
        } else {
            let raw_min = (self.0 * rhs.0).min(self.0 * rhs.1).min(self.1 * rhs.0).min(self.1 * rhs.1);
            let raw_max = (self.0 * rhs.0).max(self.0 * rhs.1).max(self.1 * rhs.0).max(self.1 * rhs.1);
            Interval(raw_min.next_down(), raw_max.next_up())
        }
    }
}

impl Div for Interval {
    type Output = Interval;

    fn div(self, rhs: Self) -> Interval {
        self * rhs.recip()
    }
}

impl Neg for Interval {
    type Output = Interval;

    fn neg(self) -> Interval {
        Interval(-self.1, -self.0)
    }
}

impl Interval {
    pub fn recip(&self) -> Self {
        let a = 1.0 / self.0;
        let b = 1.0 / self.1;
        Interval(b.next_down(), a.next_up())
    }

    #[inline]
    fn integrity_check(&self) {
        debug_assert!(!self.0.is_nan() && !self.1.is_nan());
        debug_assert!(self.0 <= self.1);
    }

    pub fn from_float(x: f64) -> Self {
        Interval(x.next_down(), x.next_up())
    }

    fn ln(&self) -> Result<Self> {
        if self.0 <= 0.0 || self.1 <= 0.0 {
            Err(anyhow!("ln of negative number"))
        } else {
            Ok(Interval(self.0.ln(), self.1.ln()))
        }
    }

    fn exp(&self) -> Self {
        Interval(self.0.exp(), self.1.exp())
    }

    pub fn pow(&self, rhs: Self) -> Result<Self> {
        Ok((rhs * self.ln()?).exp())
    }

    pub fn round_to_int(&self) -> i128 {
        let a = self.0.round();
        let b = self.1.round();
        if a == b {
            a as i128
        } else {
            panic!("interval not a single integer")
        }
    }
}

impl PartialEq for Interval {
    fn eq(&self, other: &Self) -> bool {
        self.integrity_check();
        other.integrity_check();
        self.0 == other.0 && self.1 == other.1
    }
}

impl Eq for Interval {}

impl Hash for Interval {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.integrity_check();
        self.0.to_bits().hash(state);
        self.1.to_bits().hash(state);
    }
}

impl Display for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Interval[{}, {}]", self.0, self.1)
    }
}

impl PartialOrd for Interval {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.integrity_check();
        other.integrity_check();
        if self.0 < other.0 && self.1 < other.1 {
            Some(std::cmp::Ordering::Less)
        } else if self.0 > other.0 && self.1 > other.1 {
            Some(std::cmp::Ordering::Greater)
        } else if self.0 == other.0 && self.1 == other.1 {
            Some(std::cmp::Ordering::Less)
        } else {
            None
        }
    }
}