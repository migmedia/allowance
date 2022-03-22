use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt::Debug;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Mul, Not, Sub};

use crate::error::AllowanceError::ParseError;
use crate::{error, Measure, Measure32};

/// # AllowanceValue
///
/// A 128bit wide type to hold values with an allowance ("Toleranz"). Based on
/// [Measure](./struct.Measure.html) and [Measure32](./struct.Measure32.html) with helper methods
/// to set and show values translated into mm.
/// Stores all values internally in 0.1μ.
///
/// ```rust
/// # use allowance::AllowanceValue;
/// let width = AllowanceValue::new(100.0, 0.05, -0.2);
///
/// assert_eq!(format!("{width}"), "100.00 +0.050/-0.200");
/// assert_eq!(format!("{width:?}"), "AV(100.0000 +0.0500 -0.2000)");
/// ```
/// A size-value defined in `Measure` with tolerances.
///
/// The `plus` and `minus` tolerances are in the same scale unit as the `value`.
/// `plus` is signed positiv (`+`) and `minus` is signed negative (`-`).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct AllowanceValue {
    pub value: Measure,
    pub plus: Measure32,
    pub minus: Measure32,
}

impl AllowanceValue {
    pub const ZERO: AllowanceValue = AllowanceValue {
        value: Measure::ZERO,
        plus: Measure32::ZERO,
        minus: Measure32::ZERO,
    };

    /// Creates a `AllowanceValue` with asymmetrical tolerances.
    ///
    /// Provided parameters as `f64` are interpreted as `mm`-values.
    ///
    #[inline]
    pub fn new<V, TP, TM>(value: V, plus: TP, minus: TM) -> Self
    where
        V: Into<Measure>,
        TP: Into<Measure32>,
        TM: Into<Measure32>,
    {
        let plus = plus.into();
        let minus = minus.into();
        assert!(plus >= minus);
        Self {
            value: value.into(),
            plus,
            minus,
        }
    }

    /// Creates a `AllowanceValue` with symmetrical tolerances.
    ///
    pub fn with_sym<V: Into<Measure>, T: Into<Measure32>>(value: V, tol: T) -> Self {
        let tol = tol.into();
        Self::new(value, tol, -tol)
    }

    /// narrows a `AllowanceValue` to the given tolerances.
    ///
    pub fn narrow<M: Into<Measure32>>(&self, plus: M, minus: M) -> Self {
        Self::new(self.value, plus, minus)
    }

    /// narrows a `AllowanceValue` to the given symmetric tolerances.
    ///
    pub fn narrow_sym<M: Into<Measure32>>(&self, tol: M) -> Self {
        let tol = tol.into();
        Self::new(self.value, tol, -tol)
    }

    /// returns the maximum value of this tolerance.
    ///
    pub fn upper_limit(&self) -> Measure {
        self.value + self.plus
    }

    /// returns the minimum value of this tolerance.
    ///
    pub fn lower_limit(&self) -> Measure {
        self.value + self.minus
    }

    /// returns `true`, if `this` tolerance is more narrow than the `other`.
    ///
    pub fn is_inside_of(&self, other: Self) -> bool {
        self.lower_limit() >= other.lower_limit() && self.upper_limit() <= other.upper_limit()
    }

    /// returns `true`, if `this` tolerance is less strict (around) the `other`.
    ///
    pub fn embrace<A: Into<AllowanceValue>>(&self, other: A) -> bool {
        let other = other.into();
        self.lower_limit() <= other.lower_limit() && self.upper_limit() >= other.upper_limit()
    }

    /// Inverses this `AllowanceValue`.
    /// Interchanges the `plus` and `minus` parts of this `AllowanceValue`.
    /// Same as `!value`.
    pub fn invert(&self) -> Self {
        Self {
            value: -self.value,
            plus: -self.minus,
            minus: -self.plus,
        }
    }
}

/// Inverses this `AllowanceValue`.
/// Interchanges the `plus` and `minus` parts of this `AllowanceValue`.
/// Shortcut for the `AllowanceValue.invert()`-method.
impl Not for AllowanceValue {
    type Output = AllowanceValue;

    fn not(self) -> Self::Output {
        self.invert()
    }
}

impl Add<AllowanceValue> for AllowanceValue {
    type Output = AllowanceValue;

    fn add(self, other: AllowanceValue) -> AllowanceValue {
        AllowanceValue {
            value: self.value + other.value,
            plus: self.plus + other.plus,
            minus: self.minus + other.minus,
        }
    }
}

impl Add<Measure> for AllowanceValue {
    type Output = AllowanceValue;

    fn add(self, other: Measure) -> AllowanceValue {
        AllowanceValue {
            value: self.value + other,
            plus: self.plus,
            minus: self.minus,
        }
    }
}

impl AddAssign for AllowanceValue {
    fn add_assign(&mut self, other: Self) {
        self.value += other.value;
        self.plus += other.plus;
        self.minus += other.minus;
    }
}

impl Sum for AllowanceValue {
    fn sum<I: Iterator<Item = AllowanceValue>>(iter: I) -> Self {
        iter.fold(Self::ZERO, Add::add)
    }
}

impl Sub<AllowanceValue> for AllowanceValue {
    type Output = AllowanceValue;

    fn sub(self, other: AllowanceValue) -> AllowanceValue {
        AllowanceValue {
            value: self.value - other.value,
            plus: self.plus - other.minus,
            minus: self.minus - other.plus,
        }
    }
}

impl Sub<Measure> for AllowanceValue {
    type Output = AllowanceValue;

    fn sub(self, other: Measure) -> AllowanceValue {
        AllowanceValue {
            value: self.value - other,
            plus: self.plus,
            minus: self.minus,
        }
    }
}

impl std::cmp::PartialOrd<AllowanceValue> for AllowanceValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.value.partial_cmp(&other.value) {
            Some(Ordering::Equal) => match self.minus.partial_cmp(&other.minus) {
                Some(Ordering::Equal) => self.plus.partial_cmp(&other.plus),
                x => x,
            },
            x => x,
        }
    }
}

impl std::cmp::Ord for AllowanceValue {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.value.cmp(&other.value) {
            Ordering::Equal => match self.minus.cmp(&other.minus) {
                Ordering::Equal => self.plus.cmp(&other.plus),
                x => x,
            },
            x => x,
        }
    }
}

impl Default for AllowanceValue {
    fn default() -> Self {
        Self::ZERO
    }
}

impl std::fmt::Display for AllowanceValue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let (v, t) = f.precision().map(|p| (p, p + 1)).unwrap_or((2, 3));
        let Self { value, plus, .. } = self;
        let minus = &-self.minus;
        if f.alternate() {
            return write!(f, "{value:#.v$} +{plus:#.t$}/-{minus:#.t$}");
        }
        if plus == minus {
            write!(f, "{value:.v$} +/-{plus:.t$}")
        } else {
            write!(f, "{value:.v$} +{plus:.t$}/-{minus:.t$}")
        }
    }
}

impl std::fmt::Debug for AllowanceValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AV({} +{} -{})", self.value, self.plus, -self.minus)
    }
}

/// A maybe harmful conversation. Ignores all possible allowance.  
impl From<AllowanceValue> for f64 {
    fn from(v: AllowanceValue) -> Self {
        f64::from(v.value)
    }
}

/// May be harmful
impl<V> From<V> for AllowanceValue
where
    V: Into<Measure>,
{
    fn from(f: V) -> Self {
        AllowanceValue::new(f, 0, 0)
    }
}

impl<V, T> From<(V, T)> for AllowanceValue
where
    V: Into<Measure>,
    T: Into<Measure32>,
{
    fn from(v: (V, T)) -> Self {
        let t = v.1.into();
        AllowanceValue::new(v.0, t, -t)
    }
}

impl<V, P, M> From<(V, P, M)> for AllowanceValue
where
    V: Into<Measure>,
    P: Into<Measure32>,
    M: Into<Measure32>,
{
    fn from(v: (V, P, M)) -> Self {
        AllowanceValue::new(v.0, v.1, v.2)
    }
}

impl From<AllowanceValue> for (f64, f64, f64) {
    fn from(v: AllowanceValue) -> Self {
        (v.value.into(), v.plus.into(), v.minus.into())
    }
}

macro_rules! multiply_all {
    ($($typ:ty),+) => {

        $(impl Mul<$typ> for AllowanceValue {
            type Output = Self;
            fn mul(self, rsh: $typ) -> Self {
                AllowanceValue {
                    value: self.value * rsh,
                    plus: self.plus * rsh,
                    minus: self.minus * rsh,
                }
            }
        })+
    };
}

multiply_all!(u64, u32, i64, i32);

impl<V, P, M> TryFrom<(Option<V>, Option<P>, Option<M>)> for AllowanceValue
where
    V: Into<Measure> + Debug,
    P: Into<Measure32> + Debug,
    M: Into<Measure32> + Debug,
{
    type Error = error::AllowanceError;

    fn try_from(triple: (Option<V>, Option<P>, Option<M>)) -> Result<Self, Self::Error> {
        match triple {
            (Some(v), Some(p), Some(m)) => Ok(AllowanceValue::new(v, p, m)),
            (Some(v), Some(p), None) => {
                let p = p.into();
                Ok(AllowanceValue::new(v, p, -p))
            }
            (Some(v), None, None) => Ok(AllowanceValue::new(v, 0, 0)),
            _ => Err(ParseError(format!(
                "AllowanceValue not parsable from '{:?}'",
                triple
            ))),
        }
    }
}

impl TryFrom<(Option<&i64>, Option<&i64>, Option<&i64>)> for AllowanceValue {
    type Error = error::AllowanceError;

    fn try_from(triple: (Option<&i64>, Option<&i64>, Option<&i64>)) -> Result<Self, Self::Error> {
        match triple {
            (Some(&v), Some(&p), Some(&m)) => Ok(AllowanceValue::new(v, p as i32, m as i32)),
            (Some(&v), Some(&p), None) => Ok(AllowanceValue::new(v, p as i32, -p as i32)),
            (Some(&v), None, None) => Ok(AllowanceValue::new(v, 0, 0)),
            _ => Err(ParseError(format!(
                "AllowanceValue not parsable from '{:?}'",
                triple
            ))),
        }
    }
}

impl TryFrom<&str> for AllowanceValue {
    type Error = error::AllowanceError;

    fn try_from(value: &str) -> std::result::Result<Self, Self::Error> {
        let f = value.parse::<f64>()?;
        Ok(AllowanceValue::from(f))
    }
}

impl TryFrom<String> for AllowanceValue {
    type Error = error::AllowanceError;

    fn try_from(value: String) -> std::result::Result<Self, Self::Error> {
        let f = value.parse::<f64>()?;
        Ok(AllowanceValue::from(f))
    }
}

impl TryFrom<&[i64]> for AllowanceValue {
    type Error = error::AllowanceError;

    fn try_from(value: &[i64]) -> Result<Self, Self::Error> {
        let mut iter = value.iter();
        Self::try_from((iter.next(), iter.next(), iter.next()))
    }
}

#[allow(unused_imports)]
mod should {
    use super::AllowanceValue;
    use crate::error::AllowanceError;
    use std::convert::TryFrom;

    #[test]
    fn prove_allowance_is_inside_of() {
        let o = AllowanceValue::new(2_000, 5, -10);

        assert!(!o.is_inside_of(AllowanceValue::with_sym(2_000, 5)));
        assert!(o.is_inside_of(AllowanceValue::with_sym(2_000, 20)));
        assert!(o.is_inside_of(AllowanceValue::with_sym(2_000, 10)));
        assert!(o.is_inside_of(AllowanceValue::new(1_995, 10, -5)));
    }

    #[test]
    fn prove_allowance_is_partial_ord() {
        let o = AllowanceValue::new(2_000, 5, -10);

        assert!(o < AllowanceValue::new(2_000, 5, -5));
        assert!(o < AllowanceValue::new(2_000, 10, -10));
        assert!(o > AllowanceValue::new(2_000, 2, -10));
        assert!(o > AllowanceValue::new(2_000, 20, -11));
        assert!(o >= AllowanceValue::new(2_000, 5, -10));
        assert!(o <= AllowanceValue::new(2_000, 5, -10));

        let simple: AllowanceValue = 30.0.into();
        assert!(simple < 30.01.into());
        assert!(simple > 29.0565.into());
        assert!(simple <= 30.00.into());
        assert!(simple >= 30.0.into());
    }

    #[test]
    fn display_is_adjustible() {
        let o = AllowanceValue::new(20_000, 50, -100);
        assert_eq!(format!("{o}"), String::from("2.00 +0.005/-0.010"));
        assert_eq!(format!("{o:.3}"), "2.000 +0.0050/-0.0100".to_string());
        assert_eq!(format!("{o:.4}"), "2.0000 +0.0050/-0.0100".to_string());
        assert_eq!(format!("{o:.0}"), String::from("2 +0.0/-0.0"));
        assert_eq!(format!("{o:.1}"), String::from("2.0 +0.01/-0.01"));

        let o = AllowanceValue::with_sym(20_000, 50);
        assert_eq!(format!("{o}"), String::from("2.00 +/-0.005"));
        assert_eq!(format!("{o:.0}"), String::from("2 +/-0.0"));

        let o = AllowanceValue::new(0.345, 0.010, -0.014);
        assert_eq!(format!("{o:.3}"), String::from("0.345 +0.0100/-0.0140"));
        let o = AllowanceValue::new(-0.35, 0.010, -0.014);
        assert_eq!(format!("{o:.3}"), String::from("-0.350 +0.0100/-0.0140"));

        assert_eq!(format!("{o:#}"), String::from("-3500 +100/-140"));

        assert_eq!(
            format!("{o:.3?}"),
            String::from("AV(-0.3500 +0.0100 -0.0140)")
        );
    }

    #[test]
    fn construct_consistent() {
        let o = AllowanceValue::from((2.0, 0.005, -0.01));
        assert_eq!(o.to_string(), "2.00 +0.005/-0.010".to_string())
    }

    #[test]
    fn substract() {
        let minuend = AllowanceValue::from((1000.0, 0.0, 0.0));
        let subtrahend = AllowanceValue::from((300.0, 20.0, -10.0));
        assert_eq!(minuend - subtrahend, (700.0, 10.0, -20.0).into());
        let minuend = AllowanceValue::from((1000.0, 10.0, -30.0));
        assert_eq!(minuend - subtrahend, (700.0, 20.0, -50.0).into());
    }

    #[test]
    fn invert() {
        let basis = AllowanceValue::new(20.0, 1.0, -0.5);
        let segment = AllowanceValue::new(5.0, 0.75, -0.2);
        let res = basis + !segment;
        assert_eq!(res, AllowanceValue::new(15.0, 1.2, -1.25));
        assert_eq!(basis + basis.invert(), AllowanceValue::new(0.0, 1.5, -1.5));
    }

    #[test]
    fn error() {
        use AllowanceError::ParseError;
        let a = AllowanceValue::try_from("nil");
        assert!(a.is_err(), "AllowanceValue ");
        assert_eq!(
            a.unwrap_err(),
            ParseError(String::from("invalid allowance literal"))
        );

        let a = AllowanceValue::try_from("");
        assert!(a.is_err(), "AllowanceValue ");
        assert_eq!(
            a.unwrap_err(),
            ParseError(String::from("cannot parse allowance from empty string"))
        );
    }
}
