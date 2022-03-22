use super::Measure;
use std::ops::Mul;

pub enum Unit {
    /// my-meter `μ`
    MY,
    /// millimeter `1 mm = 1000 μ`
    MM,
    /// centimeter `1 cm = 10 mm = 10_000 μ`
    CM,
    /// meter `100 cm = 1_000 mm = 1_000_000 μ`
    METER,
    /// kilometer `1 km = 1_000 m`
    KM,
    /// as exponent `10 ^ x`
    DYN(usize),
}

impl From<Unit> for Measure {
    fn from(unit: Unit) -> Self {
        Measure::from(unit.multiply())
    }
}

impl Unit {
    #[inline]
    pub fn multiply(&self) -> i64 {
        use Unit::*;
        match self {
            MY => Measure::MY,
            MM => Measure::MY * 1_000,
            CM => Measure::MY * 10_000,
            METER => Measure::MY * 1_000_000,
            KM => Measure::MY * 1_000_000_000,
            DYN(p) => (0..*p).fold(1i64, |acc, _| acc * 10),
        }
    }
}

macro_rules! unit_from_number {
    ($($typ:ident),+) => {
        $(
            impl Mul<$typ> for Unit {
                type Output = Measure;

                fn mul(self, rhs: $typ) -> Self::Output {
                    Measure::from(self.multiply() * rhs as i64)
                }
            }

             impl Mul<Unit> for $typ {
                type Output = Measure;

                fn mul(self, rhs: Unit) -> Self::Output {
                    Measure::from(rhs.multiply() * self as i64)
                }
            }
        )+
    }
}

unit_from_number!(i8, i16, i32, i64, u8, u16, u32, u64);

#[cfg(test)]
mod should {
    use crate::{Measure, Unit};

    #[test]
    fn multiply_with_number() {
        assert_eq!(Measure::from(3.0), 3 * Unit::MM);
        assert_eq!(Measure::from(55000.0), 55 * Unit::METER);
    }
}
