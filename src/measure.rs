use super::Measure32;
use super::Unit;
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt::{Debug, Display, Formatter};
use std::num::ParseFloatError;
use std::ops::{Add, AddAssign, Deref, Div, Mul, Neg, Sub, SubAssign};

///
/// # Measure
///
/// A type to calculate lossless dimensions with a fixed precision.
/// All sizes are defined in the tenth fraction of `μ`:
///
///  * 10 = 1 μ
///  * 10_000  = 1 mm
///  * 10_000_000  = 1 m
///
/// The standard `Display::fmt`-methode represents the value in `mm`. The *alternate* Display
/// shows the `i64` value.
///
/// As 10_000 = 1 mm
///
/// ### Example:
/// ```rust
///#     use allowance::Measure;
///     let measure = Measure::from(12.5);
///
///     assert_eq!(format!("{measure}"),"12.5000");
///     assert_eq!(format!("{measure:.2}"), "12.50");
///     assert_eq!(format!("{measure:#}"), "125000");
/// ```
///
///

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Measure(i64);

impl Measure {
    pub const MY: i64 = 10;
    pub const MM: Measure = Measure(1_000 * Self::MY);
    pub const ZERO: Measure = Measure(0);
    /// Holds at MAX 922_337_203 km
    pub const MAX: Measure = Measure(i64::MAX);
    /// Holds at MIN -922_337_203 km
    pub const MIN: Measure = Measure(i64::MIN);

    pub fn as_i64(&self) -> i64 {
        self.0
    }

    #[inline]
    pub fn as_mm(&self) -> f64 {
        (self.0 as f64) / Unit::MM.multiply() as f64
    }

    /// Returns the value in the given `Unit`.
    pub fn as_prec(&self, unit: Unit) -> f64 {
        (self.0 as f64) / unit.multiply() as f64
    }

    /// Rounds to the given Unit.
    pub fn round(&self, unit: Unit) -> Self {
        if unit.multiply() == 0 {
            return *self;
        }
        let m = unit.multiply();
        let clip = self.0 % m;
        match m / 2 {
            _ if clip == 0 => *self, // don't round
            x if clip <= -x => Measure(self.0 - clip - m),
            x if clip >= x => Measure(self.0 - clip + m),
            _ => Measure(self.0 - clip),
        }
    }

    pub fn floor(&self, unit: Unit) -> Self {
        let val = self.0;
        let clip = val % unit.multiply();
        Measure(val - clip)
    }
}

macro_rules! measure_from_number {
    ($($typ:ident),+) => {
        $(
            impl From<$typ> for Measure {
                fn from(a: $typ) -> Self {
                    Self(a as i64)
                }
            }

            impl From<Measure> for $typ {
                fn from(a: Measure) -> Self {
                    a.0 as $typ
                }
            }

            impl Add<$typ> for Measure {
                type Output = Measure;

                fn add(self, rhs: $typ) -> Self::Output {
                    Self(self.0 + (rhs as i64))
                }
            }

            impl AddAssign<$typ> for Measure {
                fn add_assign(&mut self, rhs: $typ) {
                    self.0 += (rhs as i64);
                }
            }

            impl Sub<$typ> for Measure {
                type Output = Measure;

                fn sub(self, rhs: $typ) -> Self::Output {
                    Self(self.0 - (rhs as i64))
                }
            }

            impl Mul<$typ> for Measure {
                type Output = Measure;

                fn mul(self, rhs: $typ) -> Self::Output {
                    Self(self.0 * (rhs as i64))
                }
            }

            impl Div<$typ> for Measure {
                type Output = Measure;

                fn div(self, rhs: $typ) -> Self::Output {
                    Self(self.0 / (rhs as i64))
                }
            }
        )+
    }
}

measure_from_number!(u64, u32, u16, u8, usize, i64, i32, i16, i8, isize);

impl From<Unit> for Measure {
    fn from(unit: Unit) -> Self {
        Measure::from(unit.multiply())
    }
}

impl From<f64> for Measure {
    fn from(f: f64) -> Self {
        assert!(
            f < i64::MAX as f64 && f > i64::MIN as f64,
            "i64 overflow, the f64 is beyond the limits of this type (Measure)."
        );
        Self((f * Measure::MM.as_i64() as f64) as i64)
    }
}

impl From<Measure> for f64 {
    fn from(f: Measure) -> Self {
        f.0 as f64 / Measure::MM.as_i64() as f64
    }
}

impl TryFrom<&str> for Measure {
    type Error = ParseFloatError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Ok(Measure::from(value.parse::<f64>()?))
    }
}

impl TryFrom<String> for Measure {
    type Error = ParseFloatError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        Ok(Measure::from(value.parse::<f64>()?))
    }
}

impl Display for Measure {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let p = f.precision().map(|p| p.min(4)).unwrap_or(4);
        assert!(p <= 4, "Measure has a limited precision of 4!");
        if f.alternate() {
            Display::fmt(&self.0, f)
        } else {
            let val = self.round(Unit::DYN(4 - p)).0;
            let l = if val.is_negative() { 6 } else { 5 };
            let mut s = format!("{val:0l$}");
            if p > 0 {
                s.insert(s.len() - 4, '.');
            }
            s.truncate(s.len() - (4 - p));
            write!(f, "{s}")
        }
    }
}

impl Debug for Measure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let val = self.0;
        let n = if val.is_negative() { 6 } else { 5 };
        let mut m = format!("{val:0n$}");
        m.insert(m.len() - 4, '.');
        write!(f, "Measure({m})")
    }
}

impl Neg for Measure {
    type Output = Measure;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Add for Measure {
    type Output = Measure;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Add<Measure32> for Measure {
    type Output = Measure;

    fn add(self, rhs: Measure32) -> Self::Output {
        Self(self.0 + rhs.as_i32() as i64)
    }
}

impl AddAssign for Measure {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl AddAssign<Measure32> for Measure {
    fn add_assign(&mut self, rhs: Measure32) {
        self.0 += rhs.as_i32() as i64;
    }
}

impl Sub for Measure {
    type Output = Measure;

    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

impl Sub<Measure32> for Measure {
    type Output = Measure;

    fn sub(self, rhs: Measure32) -> Self::Output {
        Self(self.0 - rhs.as_i32() as i64)
    }
}

impl SubAssign for Measure {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl SubAssign<Measure32> for Measure {
    fn sub_assign(&mut self, rhs: Measure32) {
        self.0 -= rhs.as_i32() as i64;
    }
}

impl Mul for Measure {
    type Output = Measure;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0)
    }
}

impl Div for Measure {
    type Output = Measure;

    fn div(self, rhs: Self) -> Self::Output {
        Self(self.0 / rhs.0)
    }
}

impl Deref for Measure {
    type Target = i64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PartialOrd for Measure {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for Measure {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

#[cfg(test)]
mod should {
    use super::*;

    #[test]
    fn cmp() {
        let s1 = Measure(200000);
        let i1 = Measure(190000);
        let s2 = Measure::from(20.0);
        let i2 = Measure::from(19.0);

        assert!(s1 > i1);
        assert_eq!(s1.partial_cmp(&i1).unwrap(), Ordering::Greater);
        assert_eq!(s1, s1);
        assert_eq!(s1.partial_cmp(&s1).unwrap(), Ordering::Equal);

        assert!(s2 > i2);
        assert_eq!(s2.partial_cmp(&i2).unwrap(), Ordering::Greater);
        assert_eq!(s2, s1);
        assert_eq!(s2.partial_cmp(&s1).unwrap(), Ordering::Equal);

        assert_eq!(i1.cmp(&s1), Ordering::Less);
        assert_eq!(i1.cmp(&i1), Ordering::Equal);
    }

    #[test]
    fn round() {
        let m = Measure(1234567);
        assert_eq!(Measure(1234570), m.round(Unit::MY));
        assert_eq!(Measure(1200000), m.round(Unit::CM));
        assert_eq!(Measure(10_000_000), Measure(9_999_000).round(Unit::MM));
        assert_eq!(Measure(0), Measure::from(-0.4993).round(Unit::MM));
        assert_eq!(Measure(-4990), Measure::from(-0.4993).round(Unit::MY));
        assert_eq!(Measure(-10000), Measure::from(-5000).round(Unit::MM));
        let m = Measure::from(340.993);
        assert_eq!(10, Unit::DYN(1).multiply());
        assert_eq!(Measure(3409930), m.round(Unit::DYN(1)));
        assert_eq!(100, Unit::DYN(2).multiply());
        assert_eq!(Measure(3409900), m.round(Unit::DYN(2)));
        assert_eq!(1000, Unit::DYN(3).multiply());
        assert_eq!(Measure(3410000), m.round(Unit::DYN(3)));
        assert_eq!(Measure(3400000), m.floor(Unit::DYN(4)));
        assert_eq!(-340.000, -340.993_f64.floor());
        assert_eq!(
            Measure(-3400000),
            Measure::from(-340.993).floor(Unit::DYN(4))
        );
    }

    #[test]
    fn display() {
        let m = Measure(12455);
        assert_eq!("1.2455", format!("{m}").as_str());
        assert_eq!("1.246", format!("{m:.3}").as_str());
        assert_eq!("1.2", format!("{m:.1}").as_str());
        assert_eq!("1.2455", format!("{m:.7}").as_str());
        assert_eq!("1", format!("{m:.0}").as_str());
        assert_eq!("-1.2455", format!("{:.7}", -m).as_str());
        let m = Measure(-455);
        assert_eq!("-0.0455", format!("{m}").as_str());
        assert_eq!("-0.3450", format!("{}", Measure(-3450)).as_str());
        assert_eq!("-455", format!("{m:#}").as_str());
        let m = Measure::from(4566.4689);
        assert_eq!(format!("{m:.3}"), "4566.469");
        let m = Measure::ZERO;
        assert_eq!(format!("{m:.2}"), "0.00");
    }

    #[test]
    fn min_max() {
        let max = Measure::MAX;
        let min = Measure::MIN;
        assert_eq!(max.0, 9223372036854775807);
        assert_eq!(min.0, -9223372036854775808);
    }

    #[test]
    fn as_prec() {
        let m = Measure::from(12456.832);
        assert_eq!(m.as_prec(Unit::CM), 1245.6832);
        assert_eq!(m.as_prec(Unit::METER), 12.456832);
        let m = Measure::MAX;
        assert_eq!(m.as_prec(Unit::KM), 922337203.6854776);
    }
}
