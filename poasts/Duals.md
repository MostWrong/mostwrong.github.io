---
title: Differentiation, and Duals
date: 2023-07-10
author: typeofemale
---


Differentiation is important, and doing differentiation with computers is even more important for building modern machine learning models at scale.

But while the topic of reverse mode automatic differentiation has been covered a billion times, in this post I wish to cover something more elegant -- dual numbers. I was planning to write a full fledged blog about the underlying maths, however this post on the AMS website [this link](https://www.ams.org/publicoutreach/feature-column/fc-2017-12) seems to be more than exhaustive for a gentle introduction on the topic. What I will be doing however is writing a basic implementation of some of these ideas in rust:

```rust
use std::collections::BTreeMap;
use std::ops::{Add, Sub, Mul, Div, AddAssign, SubAssign};
use std::fmt;
use num_traits::{Float, FromPrimitive, ToPrimitive, Pow};

#[derive(Debug, Clone)]
pub struct HyperDual<T: Float + AddAssign + SubAssign> {
    real: T,
    dual: BTreeMap<String, T>,
}

impl<T: Float + FromPrimitive + ToPrimitive + AddAssign + SubAssign> HyperDual<T> {
    pub fn new(real: T, dual: BTreeMap<String, T>) -> Self {
        HyperDual { real, dual }
    }

    pub fn get(&self, key: &str) -> T {
        *self.dual.get(key).unwrap_or(&T::zero())
    }

    pub fn set(&mut self, key: &str, value: T) {
        self.dual.insert(key.to_string(), value);
    }

    pub fn sin(self) -> Self {
        let real = self.real.sin();
        let cos_val = self.real.cos();
        let mut dual = BTreeMap::new();

        for (key, &value) in self.dual.iter() {
            dual.insert(key.clone(), cos_val * value);
        }

        HyperDual::new(real, dual)
    }

    pub fn cos(self) -> Self {
        let real = self.real.cos();
        let sin_val = self.real.sin();
        let mut dual = BTreeMap::new();

        for (key, &value) in self.dual.iter() {
            dual.insert(key.clone(), -sin_val * value);
        }

        HyperDual::new(real, dual)
    }
}

impl<T: Float + fmt::Display + AddAssign + SubAssign> fmt::Display for HyperDual<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.real)?;
        for (key, value) in self.dual.iter() {
            write!(f, " + {}{}", value, key)?;
        }
        Ok(())
    }
}

impl<T: Float + FromPrimitive + AddAssign + SubAssign> Add for HyperDual<T> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self {
        let real = self.real + rhs.real;
        let dual = self.dual.clone();

        for (key, value) in rhs.dual {
            *self.dual.entry(key).or_insert(T::zero()) += value;
        }

        HyperDual::new(real, dual)
    }
}

impl<T: Float + FromPrimitive + AddAssign + SubAssign> Sub for HyperDual<T> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self {
        let real = self.real - rhs.real;
        let dual = self.dual.clone();

        for (key, value) in rhs.dual {
            *self.dual.entry(key).or_insert(T::zero()) -= value;
        }

        HyperDual::new(real, dual)
    }
}

impl<T: Float + FromPrimitive + AddAssign + SubAssign> Mul for HyperDual<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let real = self.real * rhs.real;
        let mut dual = BTreeMap::new();

        for (key, &value) in self.dual.iter() {
            dual.insert(key.clone(), self.real * rhs.get(key) + rhs.real * value);
        }

        for (key, &value) in rhs.dual.iter() {
            if !dual.contains_key(key) {
                dual.insert(key.clone(), self.real * value);
            }
        }

        HyperDual::new(real, dual)
    }
}

impl<T: Float + FromPrimitive + AddAssign + SubAssign> Div for HyperDual<T> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        let real = self.real / rhs.real;
        let mut dual = BTreeMap::new();

        for (key, &value) in self.dual.iter() {
            dual.insert(key.clone(), (rhs.real * value - self.real * rhs.get(key)) / (rhs.real * rhs.real));
        }

        HyperDual::new(real, dual)
    }
}

impl<T: Float + FromPrimitive + AddAssign + SubAssign> std::ops::Neg for HyperDual<T> {
    type Output = Self;

    fn neg(self) -> Self {
        HyperDual::new(-self.real, self.dual.iter().map(|(k, v)| (k.clone(), -(*v))).collect())
    }
}

impl<T: Float + FromPrimitive + AddAssign + SubAssign> Pow<T> for HyperDual<T> {
    type Output = Self;

    fn pow(self, rhs: T) -> Self {
        let real = self.real.powf(rhs);
        let deriv_multiplier = rhs * self.real.powf(rhs - T::from_f64(1.0).unwrap());
        let dual = self.dual.iter().map(|(k, v)| (k.clone(), deriv_multiplier * (*v))).collect();
        
        HyperDual::new(real, dual)
    }
}

fn main() {
    let x = HyperDual::new(3.0, vec![("x".to_string(), 1.0)].into_iter().collect());
    let y = HyperDual::new(-1.0, vec![("y".to_string(), 1.0)].into_iter().collect());
    let z = HyperDual::new(2.0, vec![("z".to_string(), 1.0)].into_iter().collect());

    let w = x * y.clone() * (y * z).sin();

    println!("Result: {w}");
}
```
This should yield 2.727892280477045 + 0.9092974268256817x - 0.23101126119419035y - 1.2484405096414273z, which corresponds to f(3,-1,2) + ∇f(3,-1,2) = -3sin(-2) + [-sin(-2), 3sin(-2) - 6cos(-2), 3cos(-2)]. This result is in line with the example given on the AMS website.

This blogpost was originally meant to be an attempt at trying to formalise [this paper](https://www.cl.cam.ac.uk/~nk480/higher-order-ad.pdf) in rust -- hopefully one day I get enough time to work on it!
