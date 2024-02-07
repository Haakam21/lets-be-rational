//
// This source code resides at www.jaeckel.org/LetsBeRational.7z .
//
// ======================================================================================
// Copyright © 2013-2023 Peter Jäckel.
// 
// Permission to use, copy, modify, and distribute this software is freely granted,
// provided that this notice is preserved.
//
// WARRANTY DISCLAIMER
// The Software is provided "as is" without warranty of any kind, either express or implied,
// including without limitation any implied warranties of condition, uninterrupted use,
// merchantability, fitness for a particular purpose, or non-infringement.
// ======================================================================================
//

#include "lets_be_rational.h"

// To cross-compile on a command line, you could just use something like
//
//   i686-w64-mingw32-g++ -w -fpermissive -shared -DNDEBUG -Ofast erf_cody.cpp lets_be_rational.cpp main.cpp normaldistribution.cpp rationalcubic.cpp XLFunctions.cpp XLOper.cpp -o LetsBeRational.xll -static-libstdc++ -static-libgcc -s
//
// To compile into a shared library on non-Windows systems, you can use
//
//   g++ -fPIC -shared -DNDEBUG -Ofast erf_cody.cpp lets_be_rational.cpp main.cpp normaldistribution.cpp rationalcubic.cpp XLFunctions.cpp XLOper.cpp -o LetsBeRational.so -s
//

#if defined(_MSC_VER)
# define NOMINMAX // to suppress MSVC's definitions of min() and max()
#endif

#include "normaldistribution.h"
#include "rationalcubic.h"
#include <float.h>
#include <cmath>
#include <algorithm>
#if defined(_WIN32) || defined(_WIN64)
# include <windows.h>
#endif

#ifdef LOG_BINARY_NESTING
#include <stdio.h>
#endif

#include <assert.h>

#include <tuple>

#define TWO_PI                            6.283185307179586476925286766559005768394338798750
#define SQRT_PI_OVER_TWO                  1.253314137315500251207882642405522626503493370305  // sqrt(pi/2) to avoid misinterpretation.
#define SQRT_THREE                        1.732050807568877293527446341505872366942805253810
#define SQRT_ONE_OVER_THREE               0.577350269189625764509148780501957455647601751270
#define TWO_PI_OVER_SQRT_TWENTY_SEVEN     1.209199576156145233729385505094770488189377498728 // 2*pi/sqrt(27)
#define SQRT_THREE_OVER_THIRD_ROOT_TWO_PI 0.938643487427383566075051356115075878414688769574 // √3 / ∛(2π)
#define PI_OVER_SIX                       0.523598775598298873077107230546583814032861566563

namespace {
  static const double SQRT_DBL_EPSILON = sqrt(DBL_EPSILON);
  static const double FOURTH_ROOT_DBL_EPSILON = sqrt(SQRT_DBL_EPSILON);
  static const double EIGHTH_ROOT_DBL_EPSILON = sqrt(FOURTH_ROOT_DBL_EPSILON);
  static const double SIXTEENTH_ROOT_DBL_EPSILON = sqrt(EIGHTH_ROOT_DBL_EPSILON);
  static const double SQRT_DBL_MIN = sqrt(DBL_MIN);
  static const double SQRT_DBL_MAX = sqrt(DBL_MAX);

  // Set this to 0 if you want positive results for (positive) denormalised inputs, else to DBL_MIN.
  // Note that you cannot achieve full machine accuracy from denormalised inputs!
  static const double DENORMALISATION_CUTOFF = 0;

  static const double VOLATILITY_VALUE_TO_SIGNAL_PRICE_IS_BELOW_INTRINSIC = -DBL_MAX;
  static const double VOLATILITY_VALUE_TO_SIGNAL_PRICE_IS_ABOVE_MAXIMUM = DBL_MAX;

  inline bool is_below_horizon(double x) { return fabs(x) < DENORMALISATION_CUTOFF; } // This weeds out denormalised (a.k.a. 'subnormal') numbers.

#if defined( ENABLE_CHANGING_THE_MAXIMUM_ITERATION_COUNT ) || defined( ENABLE_CHANGING_THE_HOUSEHOLDER_METHOD_ORDER ) || defined( E )

  // See https://www.kernel.org/doc/Documentation/atomic_ops.txt for further details on this simplistic implementation of an atomic flag that is *not* volatile.
  typedef struct {
#if defined(_MSC_VER) || defined(_WIN32) || defined(_WIN64)
    long data;
#else
    int data;
#endif
  } atomic_t;

#endif

#ifdef ENABLE_CHANGING_THE_MAXIMUM_ITERATION_COUNT

  static atomic_t implied_volatility_maximum_iterations = { 2 }; // (DBL_DIG*20)/3 ≈ 100 . Only needed when the iteration effectively alternates Householder/Halley/Newton steps and binary nesting due to roundoff truncation.

# define IMPLIED_VOLATILITY_MAXIMUM_ITERATIONS implied_volatility_maximum_iterations.data

#else

# define IMPLIED_VOLATILITY_MAXIMUM_ITERATIONS 2

#endif

#if defined( ENABLE_SAFE_GUARDING_IN_HOUSEHOLDER_EXPANSIONS ) // Tests show that there is in fact no need for this
  inline double householder3_factor(double nu, double hh2, double hh3) {
    // Safeguarding against out-of-bounds behaviour comprised by a change in sign with fallback to either Halley or Newton, whichever is admissible.
    // The Halley method is ν / (1 + eta) with eta := 0.5 · h₂ · ν. It should have the same sign as ν = 'newton' by itself.
    // Hence, 1 + eta <= 0 is a clear indicator that the current guess is not inside the domain of attraction of the Halley method and we should fall back to the Newton method.
    // The Housholder(3) method is designed and intended as an improvement over the Halley method whence, if Halley is already failing the sign check, we do not even dare to look at the Housholder(3) method.
    const double eta = 0.5 * hh2 * nu;
    if (eta > -1) {
      // The Housholder(3) method is ν * (1 + eta) / (1 + zeta) with zeta := ν * (h₂ + h₃ * ν / 6), and it should also have the same sign as ν = 'newton' by itself.
      const double zeta = nu * (hh2 + hh3 * nu / 6);
      if (zeta > -1)
        return (1 + eta) / (1 + zeta);
      return 1 / (1 + eta);
    }
    return 1;
  }
#else
  inline double householder3_factor(double nu, double hh2, double hh3) { return (1 + 0.5 * hh2 * nu) / (1 + nu * (hh2 + hh3 * nu / 6)); }
#endif

  inline double householder4_factor(double nu, double hh2, double hh3, double hh4) { return (1 + nu * (hh2 + nu * hh3 / 6)) / (1 + nu * (1.5 * hh2 + nu * (hh2 * hh2 / 4 + hh3 / 3 + nu * hh4 / 24))); }

#ifdef ENABLE_CHANGING_THE_HOUSEHOLDER_METHOD_ORDER

  static atomic_t implied_volatility_maximum_householder_method_order = { 5 };

#if defined( ENABLE_SAFE_GUARDING_IN_HOUSEHOLDER_EXPANSIONS ) // Tests show that there is in fact no need for this
  inline double halley_factor(double nu, double hh2) {
    // Safeguarding against out-of-bounds behaviour comprised by a change in sign with fallback to Newton.
    // The Halley method is ν / (1 + eta) with eta := 0.5 · h₂ · ν. It should have the same sign as ν = 'newton' by itself.
    // Hence, 1 + eta <= 0 is a clear indicator that the current guess is not inside the domain of attraction of the Halley method and we should fall back to the Newton method.
    const double eta = 0.5 * hh2 * nu;
    if (eta > -1)
      return 1 / (1 + eta);
    return 1;
  }
#else
  inline double halley_factor(double nu, double hh2) { return 1 / (1 + 0.5 * hh2 * nu); }
#endif

  inline double householder_factor(double nu, double hh2, double hh3) {
    return implied_volatility_maximum_householder_method_order.data > 3 ? householder3_factor(nu, hh2, hh3) : (implied_volatility_maximum_householder_method_order.data > 2 ? halley_factor(nu, hh2) : 1);
  }
  inline double householder_factor(double nu, double hh2, double hh3, double hh4) {
    return implied_volatility_maximum_householder_method_order.data > 4 ? householder4_factor(nu, hh2, hh3, hh4) : householder_factor(nu, hh2, hh3);
  }

#else

  inline double householder_factor(double nu, double hh2, double hh3) { return householder3_factor(nu, hh2, hh3); }
  inline double householder_factor(double nu, double hh2, double hh3, double hh4) { return householder4_factor(nu, hh2, hh3, hh4); }

#endif

#ifdef ENABLE_SWITCHING_THE_OUTPUT_TO_ITERATION_COUNT

  static atomic_t implied_volatility_output_type = { 0 };

  inline double implied_volatility_output(int count, double volatility) { return implied_volatility_output_type.data != 0 ? count : volatility; }

#else

  inline double implied_volatility_output(int /* count */, double volatility) { return volatility; }

#endif  

}

#ifdef ENABLE_CHANGING_THE_MAXIMUM_ITERATION_COUNT
int set_implied_volatility_maximum_iterations(int n) {
  if (n >= 0) {
#if defined(_MSC_VER) || defined(_WIN32) || defined(_WIN64)
    long i = (long)n;
    InterlockedExchange(&(implied_volatility_maximum_iterations.data), i);
#elif defined( __x86__ ) || defined( __x86_64__ )
    implied_volatility_maximum_iterations.data = n;
#else
# error Atomic operations not implemented for this platform.
#endif
  }
  return (int)implied_volatility_maximum_iterations.data;
}
#endif

#ifdef ENABLE_CHANGING_THE_HOUSEHOLDER_METHOD_ORDER
int set_implied_volatility_householder_method_order(int order) {
  if (order >= 0) {
#if defined(_MSC_VER) || defined(_WIN32) || defined(_WIN64)
    long i = (long)order;
    InterlockedExchange(&(implied_volatility_maximum_householder_method_order.data), i);
#elif defined( __x86__ ) || defined( __x86_64__ )
    implied_volatility_maximum_householder_method_order.data = order;
#else
# error Atomic operations not implemented for this platform.
#endif
  }
  return (int)implied_volatility_maximum_householder_method_order.data;
}
#endif  

#ifdef ENABLE_SWITCHING_THE_OUTPUT_TO_ITERATION_COUNT
int set_implied_volatility_output_type(int type) {
  if (type >= 0) {
#if defined(_MSC_VER) || defined(_WIN32) || defined(_WIN64)
    long i = (long)type;
    InterlockedExchange(&(implied_volatility_output_type.data), i);
#elif defined( __x86__ ) || defined( __x86_64__ )
    implied_volatility_output_type.data = type;
#else
# error Atomic operations not implemented for this platform.
#endif
  }
  return (int)implied_volatility_output_type.data;
}
#endif  

double normalised_intrinsic(double x, double q /* q=±1 */) {
  if (q * x <= 0)
    return 0;
  const double x2 = x * x;
  if (x2 < 98 * FOURTH_ROOT_DBL_EPSILON) // The factor 98 is computed from last coefficient: √√92897280 = 98.1749
    return fabs(std::max((q < 0 ? -1 : 1) * x * (1 + x2 * ((1.0 / 24.0) + x2 * ((1.0 / 1920.0) + x2 * ((1.0 / 322560.0) + (1.0 / 92897280.0) * x2)))), 0.0));
  const double b_max = exp(0.5 * x), one_over_b_max = 1 / b_max;
  return fabs(std::max((q < 0 ? -1 : 1) * (b_max - one_over_b_max), 0.));
}

inline double normalised_intrinsic_call(double x) { return normalised_intrinsic(x, 1); }

inline double square(double x) { return x * x; }

namespace {
  /* η */ const double asymptotic_expansion_accuracy_threshold = -10;
  /* τ */ const double small_t_expansion_of_normalised_black_threshold = 2 * SIXTEENTH_ROOT_DBL_EPSILON;
}

// Asymptotic expansion of
//
//              b  =  Φ(h+t)·exp(x/2) - Φ(h-t)·exp(-x/2)
// with
//              h  =  x/s   and   t  =  s/2   for h < 0, |h| > 10, t ≲ |h| -9.8.
// which makes
//              b  =  Φ(h+t)·exp(h·t) - Φ(h-t)·exp(-h·t)
//
//                    exp(-(h²+t²)/2)
//                 =  ---------------  ·  [ Y(h+t) - Y(h-t) ]
//                        √(2π)
// with
//           Y(z) := Φ(z)/φ(z)
//
// for large negative (t-|h|) by the aid of Abramowitz & Stegun (26.2.12) where Φ(z) = φ(z)/|z|·[1-1/z^2+...].
// We define
//                     r
//         A(h,t) :=  --- · [ Y(h+t) - Y(h-t) ]
//                     t
//
// with r := (h+t)·(h-t) and give an expansion for A(h,t) in q:=(h/r)² expressed in terms of e:=(t/h)² .
//
// Note that vega = ∂(b(x,s)/∂s = exp(-(h²+t²)/2)/√(2π)
//
double asymptotic_expansion_of_normalised_black_call_over_vega(double h, double t) {
  assert(h < -fabs(asymptotic_expansion_accuracy_threshold) && h + t < -fabs(small_t_expansion_of_normalised_black_threshold + asymptotic_expansion_accuracy_threshold));
  // Note that e := (t/h)² ∈ (0,1).
  const double e = square(t / h), r = ((h + t) * (h - t)), q = square(h / r);
  // 17th order asymptotic expansion of A(h,t) in q, sufficient for Φ(z) [and thus Y(z)] to have relative accuracy of 1.64E-16 for z <= η  with  η:=-10.
  const double asymptotic_expansion_sum = (2.0 + q * (-6.0E0 - 2.0 * e + 3.0 * q * (1.0E1 + e * (2.0E1 + 2.0 * e) + 5.0 * q * (-1.4E1 + e * (-7.0E1 + e * (-4.2E1 - 2.0 * e)) + 7.0 * q * (1.8E1 + e * (1.68E2 + e * (2.52E2 + e * (7.2E1 + 2.0 * e))) + 9.0 * q * (-2.2E1 + e * (-3.3E2 + e * (-9.24E2 + e * (-6.6E2 + e * (-1.1E2 - 2.0 * e)))) + 1.1E1 * q * (2.6E1 + e * (5.72E2 + e * (2.574E3 + e * (3.432E3 + e * (1.43E3 + e * (1.56E2 + 2.0 * e))))) + 1.3E1 * q * (-3.0E1 + e * (-9.1E2 + e * (-6.006E3 + e * (-1.287E4 + e * (-1.001E4 + e * (-2.73E3 + e * (-2.1E2 - 2.0 * e)))))) + 1.5E1 * q * (3.4E1 + e * (1.36E3 + e * (1.2376E4 + e * (3.8896E4 + e * (4.862E4 + e * (2.4752E4 + e * (4.76E3 + e * (2.72E2 + 2.0 * e))))))) + 1.7E1 * q * (-3.8E1 + e * (-1.938E3 + e * (-2.3256E4 + e * (-1.00776E5 + e * (-1.84756E5 + e * (-1.51164E5 + e * (-5.4264E4 + e * (-7.752E3 + e * (-3.42E2 - 2.0 * e)))))))) + 1.9E1 * q * (4.2E1 + e * (2.66E3 + e * (4.0698E4 + e * (2.3256E5 + e * (5.8786E5 + e * (7.05432E5 + e * (4.0698E5 + e * (1.08528E5 + e * (1.197E4 + e * (4.2E2 + 2.0 * e))))))))) + 2.1E1 * q * (-4.6E1 + e * (-3.542E3 + e * (-6.7298E4 + e * (-4.90314E5 + e * (-1.63438E6 + e * (-2.704156E6 + e * (-2.288132E6 + e * (-9.80628E5 + e * (-2.01894E5 + e * (-1.771E4 + e * (-5.06E2 - 2.0 * e)))))))))) + 2.3E1 * q * (5.0E1 + e * (4.6E3 + e * (1.0626E5 + e * (9.614E5 + e * (4.08595E6 + e * (8.9148E6 + e * (1.04006E7 + e * (6.53752E6 + e * (2.16315E6 + e * (3.542E5 + e * (2.53E4 + e * (6.0E2 + 2.0 * e))))))))))) + 2.5E1 * q * (-5.4E1 + e * (-5.85E3 + e * (-1.6146E5 + e * (-1.77606E6 + e * (-9.37365E6 + e * (-2.607579E7 + e * (-4.01166E7 + e * (-3.476772E7 + e * (-1.687257E7 + e * (-4.44015E6 + e * (-5.9202E5 + e * (-3.51E4 + e * (-7.02E2 - 2.0 * e)))))))))))) + 2.7E1 * q * (5.8E1 + e * (7.308E3 + e * (2.3751E5 + e * (3.12156E6 + e * (2.003001E7 + e * (6.919458E7 + e * (1.3572783E8 + e * (1.5511752E8 + e * (1.0379187E8 + e * (4.006002E7 + e * (8.58429E6 + e * (9.5004E5 + e * (4.7502E4 + e * (8.12E2 + 2.0 * e))))))))))))) + 2.9E1 * q * (-6.2E1 + e * (-8.99E3 + e * (-3.39822E5 + e * (-5.25915E6 + e * (-4.032015E7 + e * (-1.6934463E8 + e * (-4.1250615E8 + e * (-6.0108039E8 + e * (-5.3036505E8 + e * (-2.8224105E8 + e * (-8.870433E7 + e * (-1.577745E7 + e * (-1.472562E6 + e * (-6.293E4 + e * (-9.3E2 - 2.0 * e)))))))))))))) + 3.1E1 * q * (6.6E1 + e * (1.0912E4 + e * (4.74672E5 + e * (8.544096E6 + e * (7.71342E7 + e * (3.8707344E8 + e * (1.14633288E9 + e * (2.07431664E9 + e * (2.33360622E9 + e * (1.6376184E9 + e * (7.0963464E8 + e * (1.8512208E8 + e * (2.7768312E7 + e * (2.215136E6 + e * (8.184E4 + e * (1.056E3 + 2.0 * e))))))))))))))) + 3.3E1 * (-7.0E1 + e * (-1.309E4 + e * (-6.49264E5 + e * (-1.344904E7 + e * (-1.4121492E8 + e * (-8.344518E8 + e * (-2.9526756E9 + e * (-6.49588632E9 + e * (-9.0751353E9 + e * (-8.1198579E9 + e * (-4.6399188E9 + e * (-1.6689036E9 + e * (-3.67158792E8 + e * (-4.707164E7 + e * (-3.24632E6 + e * (-1.0472E5 + e * (-1.19E3 - 2.0 * e))))))))))))))))) * q)))))))))))))))));
  // Note that vega = ∂(b(x,s)/∂s = exp(-(h²+t²)/2)/√(2π)
  const double b_over_vega = (t / r) * asymptotic_expansion_sum;
  return fabs(std::max(b_over_vega, 0.));
}

double normalised_black_call_using_erfcx(double h, double t) {
  // Given h = x/s and t = s/2, the normalised Black function can be written as
  //
  //     b(x,s)  =  Φ(x/s+s/2)·exp(x/2)  -   Φ(x/s-s/2)·exp(-x/2)
  //             =  Φ(h+t)·exp(h·t)      -   Φ(h-t)·exp(-h·t) .                     (*)
  //
  // It is mentioned in section 4 (and discussion of figures 2 and 3) of George Marsaglia's article "Evaluating the
  // Normal Distribution" (available at http://www.jstatsoft.org/v11/a05/paper) that the error of any cumulative normal
  // function Φ(z) is dominated by the hardware (or compiler implementation) accuracy of exp(-z²/2) which is not
  // reliably more than 14 digits when z is large. The accuracy of Φ(z) typically starts coming down to 14 digits when
  // z is around -8. For the (normalised) Black function, as above in (*), this means that we are subtracting two terms
  // that are each products of terms with about 14 digits of accuracy. The net result, in each of the products, is even
  // less accuracy, and then we are taking the difference of these terms, resulting in even less accuracy. When we are
  // using the asymptotic expansion asymptotic_expansion_of_normalised_black_call_over_vega() invoked in the second branch at the
  // beginning of this function, we are using only *one* exponential instead of 4, and this improves accuracy. It
  // actually improves it a bit more than you would expect from the above logic, namely, almost the full two missing
  // digits (in 64 bit IEEE floating point).  Unfortunately, going higher order in the asymptotic expansion will not
  // enable us to gain more accuracy (by extending the range in which we could use the expansion) since the asymptotic
  // expansion, being a divergent series, can never gain 16 digits of accuracy for z=-8 or just below. The best you can
  // get is about 15 digits (just), for about 35 terms in the series (26.2.12), which would result in an prohibitively
  // long expression in function asymptotic expansion asymptotic_expansion_of_normalised_black_call_over_vega(). In this last branch,
  // here, we therefore take a different tack as follows.
  //     The "scaled complementary error function" is defined as erfcx(z) = exp(z²)·erfc(z). Cody's implementation of this
  // function as published in "Rational Chebyshev approximations for the error function", W. J. Cody, Math. Comp., 1969, pp.
  // 631-638, uses rational functions that theoretically approximates erfcx(x) to at least 18 significant decimal digits,
  // *without* the use of the exponential function when x>4, which translates to about z<-5.66 in Φ(z). To make use of it,
  // we write
  //             Φ(z) = exp(-z²/2)·erfcx(-z/√2)/2
  //
  // to transform the normalised black function to
  //
  //   b   =  ½ · exp(-½(h²+t²)) · [ erfcx(-(h+t)/√2) -  erfcx(-(h-t)/√2) ]
  //
  // which now involves only one exponential, instead of three, when |h|+|t| > 5.66 , and the difference inside the
  // square bracket is between the evaluation of two rational functions, which, typically, according to Marsaglia,
  // retains the full 16 digits of accuracy (or just a little less than that).
  //
  const double b = 0.5 * exp(-0.5 * (h * h + t * t)) * (erfcx_cody(-(1 / SQRT_TWO) * (h + t)) - erfcx_cody(-(1 / SQRT_TWO) * (h - t)));
  return fabs(std::max(b, 0.0));
}

// Calculation of
//
//              b  =  Φ(h+t)·exp(h·t) - Φ(h-t)·exp(-h·t)
//
//                    exp(-(h²+t²)/2)
//                 =  --------------- ·  [ Y(h+t) - Y(h-t) ]
//                        √(2π)
// with
//           Y(z) := Φ(z)/φ(z)
//
// using an expansion of Y(h+t)-Y(h-t) for small t to twelvth order in t.
// Theoretically accurate to (better than) precision  ε = 2.23E-16  when  h<=0  and  t < τ  with  τ := 2·ε^(1/16) ≈ 0.21.
// The main bottleneck for precision is the coefficient a:=1+h·Y(h) when |h|>1 .
//
// Note that vega = ∂(b(x,s)/∂s = exp(-(h²+t²)/2)/√(2π)
//
double small_t_expansion_of_normalised_black_call_over_vega(double h, double t) {
  // Y(h) := Φ(h)/φ(h) = √(π/2)·erfcx(-h/√2)
  // a := 1+h·Y(h)  --- Note that due to h<0, and h·Y(h) -> -1 (from above) as h -> -∞, we also have that a>0 and a -> 0 as h -> -∞
  // w := t² , h2 := h²
  const double a = 1 + h * SQRT_PI_OVER_TWO * erfcx_cody(-(1 / SQRT_TWO) * h), w = t * t, h2 = h * h;
  const double b_over_vega = 2 * t * (a + w * ((-1 + 3 * a + a * h2) / 6 + w * ((-7 + 15 * a + h2 * (-1 + 10 * a + a * h2)) / 120 + w * ((-57 + 105 * a + h2 * (-18 + 105 * a + h2 * (-1 + 21 * a + a * h2))) / 5040 + w * ((-561 + 945 * a + h2 * (-285 + 1260 * a + h2 * (-33 + 378 * a + h2 * (-1 + 36 * a + a * h2)))) / 362880 + w * ((-6555 + 10395 * a + h2 * (-4680 + 17325 * a + h2 * (-840 + 6930 * a + h2 * (-52 + 990 * a + h2 * (-1 + 55 * a + a * h2))))) / 39916800 + ((-89055 + 135135 * a + h2 * (-82845 + 270270 * a + h2 * (-20370 + 135135 * a + h2 * (-1926 + 25740 * a + h2 * (-75 + 2145 * a + h2 * (-1 + 78 * a + a * h2)))))) * w) / 6227020800.0))))));
  return fabs(std::max(b_over_vega, 0.0));
}

//     b(x,s)  =  Φ(x/s+s/2)·exp(x/2)  -   Φ(x/s-s/2)·exp(-x/2)
//             =  Φ(h+t)·exp(x/2)      -   Φ(h-t)·exp(-x/2)
// with
//              h  =  x/s   and   t  =  s/2
double normalised_black_call_using_norm_cdf(double x, double s) {
  const double h = x / s, t = 0.5 * s, b_max = exp(0.5 * x), b = norm_cdf(h + t) * b_max - norm_cdf(h - t) / b_max;
  return fabs(std::max(b, 0.0));
}

//
// Introduced on 2017-02-18
//
//     b(x,s)  =  Φ(x/s+s/2)·exp(x/2)  -   Φ(x/s-s/2)·exp(-x/2)
//             =  Φ(h+t)·exp(x/2)      -   Φ(h-t)·exp(-x/2)
//             =  ½ · exp(-u²-v²) · [ erfcx(u-v) -  erfcx(u+v) ]
//             =  ½ · [ exp(x/2)·erfc(u-v)     -  exp(-x/2)·erfc(u+v)    ]
//             =  ½ · [ exp(x/2)·erfc(u-v)     -  exp(-u²-v²)·erfcx(u+v) ]
//             =  ½ · [ exp(-u²-v²)·erfcx(u-v) -  exp(-x/2)·erfc(u+v)    ]
// with
//              h  =  x/s ,       t  =  s/2 ,
// and
//              u  = -h/√2  and   v  =  t/√2 .
//
// Cody's erfc() and erfcx() functions each, for some values of their argument, involve the evaluation
// of the exponential function exp(). The normalised Black function requires additional evaluation(s)
// of the exponential function irrespective of which of the above formulations is used. However, the total
// number of exponential function evaluations can be minimised by a judicious choice of one of the above
// formulations depending on the input values and the branch logic in Cody's erfc() and erfcx().
//
double normalised_black_call_with_optimal_use_of_codys_functions(double x, double s) {
  const double codys_threshold = 0.46875, h = x / s, t = 0.5 * s, q1 = -(1 / SQRT_TWO) * (h + t), q2 = -(1 / SQRT_TWO) * (h - t);
  double two_b;
  if (q1 < codys_threshold)
    if (q2 < codys_threshold)
      two_b = exp(0.5 * x) * erfc_cody(q1) - exp(-0.5 * x) * erfc_cody(q2);
    else
      two_b = exp(0.5 * x) * erfc_cody(q1) - exp(-0.5 * (h * h + t * t)) * erfcx_cody(q2);
  else
    if (q2 < codys_threshold)
      two_b = exp(-0.5 * (h * h + t * t)) * erfcx_cody(q1) - exp(-0.5 * x) * erfc_cody(q2);
    else
      two_b = exp(-0.5 * (h * h + t * t)) * (erfcx_cody(q1) - erfcx_cody(q2));
  return fabs(std::max(0.5 * two_b, 0.0));
}

// ∂b(x,s)/∂s = b'(s) = exp(-½·((x/s)²+(s/2)²) / √(2π)
double normalised_vega(double x, double s) {
  const double ax = fabs(x);
  return (ax <= 0) ? (1 / SQRT_TWO_PI) * exp(-0.125 * s * s) : ((s <= 0 || s <= ax * SQRT_DBL_MIN) ? 0 : (1 / SQRT_TWO_PI) * exp(-0.5 * (square(x / s) + square(0.5 * s))));
}

double ln_normalised_vega(double x, double s) {
  return (fabs(x) <= 0) ? (-(LN_TWO_PI / 2) - 0.125 * (s * s)) : (s <= 0) ? -DBL_MAX : (-(LN_TWO_PI / 2) - 0.5 * (square(x / s) + square(0.5 * s)));
}

double normalised_black_call(double x, double s) {
  if (x > 0)
    return normalised_intrinsic_call(x) + normalised_black_call(-x, s); // In the money.
  if (s <= fabs(x) * DENORMALISATION_CUTOFF)
    return normalised_intrinsic_call(x); // sigma=0 -> intrinsic value.
  // Denote h := x/s and t := s/2. We evaluate the condition |h|>|η|, i.e., h<η  &&  t < τ+|h|-|η|  avoiding any divisions by s , where η = asymptotic_expansion_accuracy_threshold  and τ = small_t_expansion_of_normalised_black_threshold .
  if (x < s * asymptotic_expansion_accuracy_threshold && 0.5 * s * s + x < s * (small_t_expansion_of_normalised_black_threshold + asymptotic_expansion_accuracy_threshold))
    return asymptotic_expansion_of_normalised_black_call_over_vega(x / s, 0.5 * s) * normalised_vega(x, s);
  if (0.5 * s < small_t_expansion_of_normalised_black_threshold)
    return small_t_expansion_of_normalised_black_call_over_vega(x / s, 0.5 * s) * normalised_vega(x, s);
#ifdef DO_NOT_OPTIMISE_NORMALISED_BLACK_IN_REGIONS_3_AND_4_FOR_CODYS_FUNCTIONS
  // When b is more than, say, about 85% of b_max=exp(x/2), then b is dominated by the first of the two terms in the Black formula, and we retain more accuracy by not attempting to combine the two terms in any way.
  // We evaluate the condition h+t>0.85  avoiding any divisions by s.
  if (x + 0.5 * s * s > s * 0.85)
    return normalised_black_call_using_norm_cdf(x, s);
  return normalised_black_call_using_erfcx(x / s, 0.5 * s);
#else
  return normalised_black_call_with_optimal_use_of_codys_functions(x, s);
#endif
}

std::tuple<double, double> normalised_black_call_over_vega_and_ln_vega(double x, double s) {
  if (x > 0) {  // In the money.
    // Structured bindings trigger a waning about the need for -std=c++17 with some older versions of g++. I don't like the tuple syntax: I very much prefer structured binding syntax, but I dislike warnings even more.
#if __cplusplus >= 201703L
    const auto [bx, ln_vega] = normalised_black_call_over_vega_and_ln_vega(-x, s);
#else
    const auto bx_and_ln_vega = normalised_black_call_over_vega_and_ln_vega(-x, s);
    const double bx = std::get<0>(bx_and_ln_vega), ln_vega = std::get<1>(bx_and_ln_vega);
#endif
    return { normalised_intrinsic_call(x) * exp(-ln_vega) + bx, ln_vega };
  }
  const double ln_vega = ln_normalised_vega(x, s);
  if (s <= fabs(x) * DENORMALISATION_CUTOFF) // sigma=0 -> intrinsic value.
    return { normalised_intrinsic_call(x) * exp(-ln_vega), ln_vega };
  // Denote h := x/s and t := s/2. We evaluate the condition |h|>|η|, i.e., h<η  &&  t < τ+|h|-|η|  avoiding any divisions by s , where η = asymptotic_expansion_accuracy_threshold  and τ = small_t_expansion_of_normalised_black_threshold .
  if (x < s * asymptotic_expansion_accuracy_threshold && 0.5 * s * s + x < s * (small_t_expansion_of_normalised_black_threshold + asymptotic_expansion_accuracy_threshold))
    return { asymptotic_expansion_of_normalised_black_call_over_vega(x / s, 0.5 * s), ln_vega };
  if (0.5 * s < small_t_expansion_of_normalised_black_threshold)
    return { small_t_expansion_of_normalised_black_call_over_vega(x / s, 0.5 * s), ln_vega };
  return { normalised_black_call_with_optimal_use_of_codys_functions(x, s) * exp(-ln_vega), ln_vega };
}

// ∂²b(x,s)/∂s²
double normalised_volga(double x, double s) {
  const double ax = fabs(x);
  if (ax <= 0) return (1 / SQRT_TWO_PI) * exp(-0.125 * s * s);
  if (s <= 0 || s <= ax * SQRT_DBL_MIN) return 0;
  const double h_sqr = square(x / s), t_sqr = square(0.5 * s);
  return (1 / SQRT_TWO_PI) * exp(-0.5 * (h_sqr + t_sqr)) * (h_sqr - t_sqr) / s;
}

double NormalisedBlack(double x, double s, double theta /* theta=±1 */) { return normalised_black_call(theta < 0 ? -x : x, s); /* Reciprocal-strike call-put equivalence */ }

double Black(double F, double K, double sigma, double T, double q /* q=±1 */) {
  const double intrinsic = fabs(std::max((q < 0 ? K - F : F - K), 0.0));
  // Map in-the-money to out-of-the-money
  if (q * (F - K) > 0)
    return intrinsic + Black(F, K, sigma, T, -q);
  return std::max(intrinsic, (sqrt(F) * sqrt(K)) * NormalisedBlack(log(F / K), sigma * sqrt(T), q));
}

#ifdef COMPUTE_LOWER_MAP_DERIVATIVES_INDIVIDUALLY
double f_lower_map(const double x, const double s) {
  if (is_below_horizon(x))
    return 0;
  if (is_below_horizon(s))
    return 0;
  const double z = SQRT_ONE_OVER_THREE * fabs(x) / s, Phi = norm_cdf(-z);
  return TWO_PI_OVER_SQRT_TWENTY_SEVEN * fabs(x) * (Phi * Phi * Phi);
}
double d_f_lower_map_d_beta(const double x, const double s) {
  if (is_below_horizon(s))
    return 1;
  const double z = SQRT_ONE_OVER_THREE * fabs(x) / s, y = z * z, Phi = norm_cdf(-z);
  return TWO_PI * y * (Phi * Phi) * exp(y + 0.125 * s * s);
}
double d2_f_lower_map_d_beta2(const double x, const double s) {
  const double ax = fabs(x), z = SQRT_ONE_OVER_THREE * ax / s, y = z * z, s2 = s * s, Phi = norm_cdf(-z), phi = norm_pdf(z);
  return PI_OVER_SIX * y / (s2 * s) * Phi * (8 * SQRT_THREE * s * ax + (3 * s2 * (s2 - 8) - 8 * x * x) * Phi / phi) * exp(2 * y + 0.25 * s2);
}
void compute_f_lower_map_and_first_two_derivatives(const double x, const double s, double& f, double& fp, double& fpp) {
  f = f_lower_map(x, s);
  fp = d_f_lower_map_d_beta(x, s);
  fpp = d2_f_lower_map_d_beta2(x, s);
}
#else
void compute_f_lower_map_and_first_two_derivatives(const double x, const double s, double& f, double& fp, double& fpp) {
  const double ax = fabs(x), z = SQRT_ONE_OVER_THREE * ax / s, y = z * z, s2 = s * s, Phi = norm_cdf(-z), phi = norm_pdf(z);
  fpp = PI_OVER_SIX * y / (s2 * s) * Phi * (8 * SQRT_THREE * s * ax + (3 * s2 * (s2 - 8) - 8 * x * x) * Phi / phi) * exp(2 * y + 0.25 * s2);
  if (is_below_horizon(s)) {
    fp = 1;
    f = 0;
  } else {
    const double Phi2 = Phi * Phi;
    fp = TWO_PI * y * Phi2 * exp(y + 0.125 * s * s);
    if (is_below_horizon(x))
      f = 0;
    else
      f = TWO_PI_OVER_SQRT_TWENTY_SEVEN * ax * (Phi2 * Phi);
  }
}
#endif

// Formula (4.38)
double inverse_f_lower_map(const double x, const double f) {
  // Caution: this can result in unnecessary underflow when f ≈ DBL_MIN and |x| is large. It also triggers 'unsafe-math-optimizations' issues with g++, exposed when -Ofast or -fast-math is used.
  //   return is_below_horizon(f) ? 0 : fabs(x / (SQRT_THREE * inverse_norm_cdf(std::pow(f / (TWO_PI_OVER_SQRT_TWENTY_SEVEN * fabs(x)), 1. / 3.))));
  return is_below_horizon(f) ? 0 : fabs(x / (SQRT_THREE * inverse_norm_cdf(SQRT_THREE_OVER_THIRD_ROOT_TWO_PI * std::cbrt(f) / std::cbrt(fabs(x)))));
}

#ifdef COMPUTE_UPPER_MAP_DERIVATIVES_INDIVIDUALLY
double f_upper_map(const double s) {
  return norm_cdf(-0.5 * s);
}
double d_f_upper_map_d_beta(const double x, const double s) {
  return is_below_horizon(x) ? -0.5 : -0.5 * exp(0.5 * square(x / s));
}
double d2_f_upper_map_d_beta2(const double x, const double s) {
  if (is_below_horizon(x))
    return 0;
  const double w = square(x / s);
  return SQRT_PI_OVER_TWO * exp(w + 0.125 * s * s) * w / s;
}
void compute_f_upper_map_and_first_two_derivatives(const double x, const double s, double& f, double& fp, double& fpp) {
  f = f_upper_map(s);
  fp = d_f_upper_map_d_beta(x, s);
  fpp = d2_f_upper_map_d_beta2(x, s);
}
#else
void compute_f_upper_map_and_first_two_derivatives(const double x, const double s, double& f, double& fp, double& fpp) {
  f = norm_cdf(-0.5 * s);
  if (is_below_horizon(x)) {
    fp = -0.5;
    fpp = 0;
  } else {
    const double w = square(x / s);
    fp = -0.5 * exp(0.5 * w);
    fpp = SQRT_PI_OVER_TWO * exp(w + 0.125 * s * s) * w / s;
  }
}
#endif

inline double inverse_f_upper_map(double f) { return -2. * inverse_norm_cdf(f); }

inline double take_step(double x_min, double x_max, double x, double& dx) {
  const double new_x = std::max(x_min, std::min(x_max, x + dx));
  dx = new_x - x;
  return new_x;
}

//
// Introduced on 2023-12-10
// 
//    b̄(x,s,θ)          :=   bₘₐₓ(x,θ)   -  b(x,s,θ)
//                       =   exp(θ·x/2)  -  θ·[ eˣ𝄍²·Φ(θ·(x/s+s/2)) - e⁻ˣ𝄍²·Φ(θ·(x/s-s/2)) ]            using  bₘₐₓ = exp(θ·x/2)
//
//                           ⎧   eˣ𝄍²·[1-Φ(x/s+s/2)] + e⁻ˣ𝄍²·Φ(x/s-s/2)                                  when θ = +1
//                       =   ⎨ 
//                           ⎩   eˣ𝄍²·Φ(-x/s-s/2)    + e⁻ˣ𝄍²·[1-Φ(-x/s+s/2)]                             when θ = -1
// using  1-Φ(z) = Φ(-z)
//                       =   eˣ𝄍²·Φ(-x/s-s/2) + e⁻ˣ𝄍²·Φ(x/s-s/2)                            (1)          for both θ = ±1
// 
// Note: no subtractive cancellation, and no dependency on θ = ±1 !
// 
//    b̄(x,s)    =   ½ · [ erfc((s/2+x/s)/√2)·eˣ𝄍² + erfc((s/2-x/s)/√2)·e⁻ˣ𝄍² ]              (2)          using  Φ(z) = erfc(-z/√2)/2
//
// using erfc(z) = erfcx(z)·exp(-z²)
// 
//    b̄(x,s)    =   ½ · ( erfcx((s/2+x/s)/√2)·exp(-½((x/s)²+x+(s/2)²))·eˣ𝄍² + erfcx((s/2-x/s)/√2)·exp(-½((x/s)²-x+(s/2)²))·e⁻ˣ𝄍² )
//
//              =   ½ · ( erfcx((s/2+x/s)/√2) + erfcx((s/2-x/s)/√2) ) · exp(-½((x/s)²+(s/2)²))
//
//              =   √(π/2) · [ erfcx((s/2+x/s)/√2) + erfcx((s/2-x/s)/√2) ] · ∂b(x,s)/∂s
//
inline double complementary_normalised_black(double h /* = x/s */, double t /* = s/2 */) {
  //    b̄(x,s)    =   ½ · ( erfcx((s/2+x/s)/√2) + erfcx((s/2-x/s)/√2) ) · exp(-½((x/s)²+(s/2)²))
  //    b̄(x,s)    =   ½ · ( erfcx((t+h)/√2) + erfcx((t-h)/√2) ) · exp(-½(t²+h²))
  return 0.5 * (erfcx_cody((t + h) * (1 / SQRT_TWO)) + erfcx_cody((t - h) * (1 / SQRT_TWO))) * exp(-0.5 * (t * t + h * h));
}

// See http://en.wikipedia.org/wiki/Householder%27s_method for a detailed explanation of the third order Householder iteration.
//
// Given the objective function g(s) whose root x such that 0 = g(s) we seek, iterate
//
//     s_n+1  =  s_n  -  (g/g') · [ 1 - (g''/g')·(g/g') ] / [ 1 - (g/g')·( (g''/g') - (g'''/g')·(g/g')/6 ) ]
//
// Denoting  ν:=-(g/g'), h₂:=(g''/g'), and hh3:=(g'''/g'), this reads
//
//     s_n+1  =  s_n  +  ν · ( 1 + ν·h₂/2 ) / ( 1 + ν·( h₂ + ν·h₃/6 ) ).
//
//
// NOTE that this function returns 0 when 𝛽 < intrinsic without any safety checks.
//
double unchecked_normalised_implied_volatility_from_a_transformed_rational_guess_with_limited_iterations(double beta, double x, double q /* q=±1 */, int N) {
  // Subtract intrinsic.
  if (q * x > 0) {
    beta = fabs(std::max(beta - normalised_intrinsic(x, q), 0.));
    q = -q;
  }
  // Map puts to calls
  if (q < 0) {
    x = -x;
    q = -q;
  }
  assert(x <= 0);
  if (beta <= 0) // For negative or zero prices we return 0.
    return implied_volatility_output(0, 0);
  if (beta < DENORMALISATION_CUTOFF) // For positive but denormalised (a.k.a. 'subnormal') prices, we return 0 since it would be impossible to converge to full machine accuracy anyway.
    return implied_volatility_output(0, 0);
  const double b_max = exp(0.5 * x);
  if (beta >= b_max)
    return implied_volatility_output(0, VOLATILITY_VALUE_TO_SIGNAL_PRICE_IS_ABOVE_MAXIMUM);
  int iterations = 0;
#if defined (ENABLE_CHANGING_THE_MAXIMUM_ITERATION_COUNT)
  int direction_reversal_count = 0;
  double ds_previous = 0;
#endif
  double f = -DBL_MAX, s = -DBL_MAX, ds = -DBL_MAX, s_left = DBL_MIN, s_right = DBL_MAX;
  // The temptation is great to use the optimised form b_c = eˣ𝄍²/2-e⁻ˣ𝄍²·Phi(sqrt(-2·x)) but that would require implementing all of the above types of round-off and over/underflow handling for this expression, too.
  const double s_c = sqrt(fabs(2 * x)), b_c = normalised_black_call(x, s_c), v_c = normalised_vega(x, s_c);
  // Four branches.
  if (beta < b_c) {
    // sc  =  √(2|x|)
    // bc  =  b(x,sc)  =  eˣ𝄍²·Φ(-√|x|/√2+√|x|/√2) - e⁻ˣ𝄍²·Φ(-√|x|/√2-√|x|/√2)  =  ½·eˣ𝄍² - e⁻ˣ𝄍²·Φ(-√(2|x|))
    // sₗ   =   sc - b(s,sc)/b'(x,sc)  =  √(2|x|) - (eˣ𝄍²·Φ(0) - e⁻ˣ𝄍²·Φ(-√(2|x|)))·exp((|x|/2+|x|/2)/2)·√(2π)   =   √(2|x|) - (½·eˣ - Φ(-√(2|x|)))·√(2π)
    // b(x,sₗ) = b(x,sₗ)
    const double s_l = s_c - b_c / v_c, b_l = normalised_black_call(x, s_l);
    if (beta < b_l) {
      {
        double f_lower_map_l, d_f_lower_map_l_d_beta, d2_f_lower_map_l_d_beta2;
        compute_f_lower_map_and_first_two_derivatives(x, s_l, f_lower_map_l, d_f_lower_map_l_d_beta, d2_f_lower_map_l_d_beta2);
        const double r_ll = convex_rational_cubic_control_parameter_to_fit_second_derivative_at_right_side(0., b_l, 0., f_lower_map_l, 1., d_f_lower_map_l_d_beta, d2_f_lower_map_l_d_beta2, true);
        f = rational_cubic_interpolation(beta, 0., b_l, 0., f_lower_map_l, 1., d_f_lower_map_l_d_beta, r_ll);
        if (!(f > 0)) { // This can happen due to roundoff truncation for extreme values such as |x|>500.
          // We switch to quadratic interpolation using f(0)≡0, f(bₗ), and f'(0)≡1 to specify the quadratic.
          const double t = beta / b_l;
          f = (f_lower_map_l * t + b_l * (1 - t)) * t;
        }
        s = inverse_f_lower_map(x, f);
        s_right = s_l;
      }
      //
      // In this branch, which comprises the lowest segment, the objective function is
      //     g(s) = 1/ln(b(x,s)) - 1/ln(𝛽)
      //          ≡ 1/ln(b(s)) - 1/ln(𝛽)
      // This makes
      //              g'                =   -b'/(b·ln(b)²)
      // using λ:=1/ln(b)
      //              g'                =   -b'/b·λ²
      //              ν      = -g/g'    =   (ln(𝛽)-ln(b))·ln(b)/ln(𝛽)·b/b'
      //                                =   (ln(𝛽)-1/λ)/(ln(𝛽)·λ) · b/b'     =   (λ-1/ln(𝛽))·b/(b'·λ²)
      //              h₂     = g''/g'   =   b''/b'  -  b'/b·(1+2/ln(b))
      //                                =   b''/b'  -  b'/b·(1+2·λ)
      //              h₃     = g'''/g'  =   b'''/b' +  2(b'/b)²·(1+3/ln(b)·(1+1/ln(b)))  -  3(b''/b)·(1+2/ln(b))
      //                                =   b'''/b' +  (b'/b)²·(2+6·λ·(1+λ))  -  (b''/b)·3·(1+2·λ)
      //              h₄     = g''''/g' =   b''''/b' - (b'/b)³·(6+λ·(22+λ·(36+λ·24))) + (b'/b)·(b''/b)·(12+36·λ·(1+λ)) - (b''/b)·(b''/b')·(3+6·λ)  - (b'''/b)·(4+8·λ)
      //                                =   b''''/b' - (b'/b)·[ (b'/b)²·(6+λ·(22+λ·(36+λ·24))) - (b''/b)·(12+36·λ·(1+λ)) ] - (b''/b)·(b''/b')·3·(1+2·λ)  - (b'''/b)·4·(1+2·λ)
      //                                =   b_h₄ - (b'/b) · [ (b'/b)²·(6+λ·(22+λ·(36+λ·24))) - (b''/b)·(12+36·λ·(1+λ)) ] - (b''/b)·b_h₂·3·(1+2·λ)  - (b'''/b)·4·(1+2·λ)
      // The Householder(3) iteration is
      //     s_n+1  =  s_n  +  ν · ( 1 + ν·h₂/2 ) / ( 1 + ν·( h₂ + ν·h₃/6 ) ).
      //
      const double ln_beta = log(beta);
      for (; iterations<N && fabs(ds)>DBL_EPSILON * s; ++iterations) {
#if defined (ENABLE_CHANGING_THE_MAXIMUM_ITERATION_COUNT)
        if (ds * ds_previous < 0)
          ++direction_reversal_count;
        if (N > 3 && iterations > 0 && (3 == direction_reversal_count || !(s > s_left && s < s_right))) {
          // If looping inefficently, or the forecast step takes us outside the bracket, or onto its edges, switch to binary nesting.
          // NOTE that this can only really happen for very extreme values of |x|, such as |x| = |ln(F/K)| > 500.
#ifdef LOG_BINARY_NESTING
          if (direction_reversal_count > 2)
            printf("Intercepting excessive direction reversal in lowest branch.\n");
          else
            printf("Intercepting bracket boundary contact/violation in lowest branch.\n");
#endif
          s = 0.5 * (s_left + s_right);
          if (s_right - s_left <= DBL_EPSILON * s) break;
          direction_reversal_count = 0;
          ds = 0;
        }
        ds_previous = ds;
#endif
        // Structured bindings trigger a waning about the need for -std=c++17 with some older versions of g++. I don't like the tuple syntax: I very much prefer structured binding syntax, but I dislike warnings even more.
#if __cplusplus >= 201703L
        const auto [bx, ln_vega] = normalised_black_call_over_vega_and_ln_vega(x, s);
#else
        const auto bx_and_ln_vega = normalised_black_call_over_vega_and_ln_vega(x, s);
        const double bx = std::get<0>(bx_and_ln_vega), ln_vega = std::get<1>(bx_and_ln_vega);
#endif
        const double ln_b = log(bx) + ln_vega, bpob = 1 / bx;
#if defined (ENABLE_CHANGING_THE_MAXIMUM_ITERATION_COUNT)
        const double b = exp(ln_b), bp = bpob * b;
        if (b > beta && s < s_right) s_right = s; else if (b<beta && s>s_left) s_left = s; // Tighten the bracket if applicable.
        if (!(b > 0 && bp > 0)) { // Numerical underflow. Switch to binary nesting for this iteration.
#ifdef LOG_BINARY_NESTING
          printf("Binary nesting in lowest branch: b=%g, b'=%g.\n", b, bp);
#endif
          ds = 0.5 * (s_left + s_right) - s;
        } else
#endif
        {
          const double h = x / s, b_hh2 = h * h / s - s / 4, nu = (ln_beta - ln_b) * ln_b / ln_beta / bpob, lambda = 1 / ln_b, otlambda = 1 + 2 * lambda, hh2 = b_hh2 - bpob * otlambda, c = 3 * square(h / s);
          const double b_hh3 = b_hh2 * b_hh2 - c - 0.25, sq_bpob = square(bpob), bppob = b_hh2 * bpob, mu = 6 * lambda * (1 + lambda), hh3 = b_hh3 + sq_bpob * (2 + mu) - bppob * 3 * otlambda;
          //
          // Introduced on 2023-12-14: for very large moneyness ratios [of no commercial relevance: exp(-190) = 3.05E-83], with exactly two Householder(3) iterations, I noticed that there is systematically a
          // residual inaccuracy in this branch [0 < b < bₗ] higher than the theoretically attainable one given by (|b(s)/(s·b'(s))|+1)·ε where ε is DBL_EPSILON and b(s) is the normalised Black function.
          // This residual inaccuracy disappears when we use two Householder(4) [5th order accuracy] iterations instead. Tests show that the initial guess is always close enough for the method to be contractive.
          // See further down in the description of the BlackAccuracyFactor() for a derivation of the formula (|b(s)/(s·b'(s))|+1)·ε. In this branch, we find that (|b(s)/(s·b'(s))|+1) is numerically equal to 1,
          // and thus the theoretically attainable relative accuracy is DBL_EPSILON.
          // 
          if (x < -190) {
            //  b_h₄   =    b''''/b'   =   b_h₂·(b_h₃-½) - (b_h₂-2/s)·6·x²/s⁴
            //   h₄    =    b_h₄ - (b'/b) · [ (b'/b)²·(6+λ·(22+λ·(36+λ·24))) - (b''/b)·(12+36·λ·(1+λ)) ] - (b''/b)·b_h₂·3·(1+2·λ)  - (b'''/b)·4·(1+2·λ)    with    λ=1/ln(b)
            ds = nu * householder_factor(nu, hh2, hh3, (b_hh2 * (b_hh3 - 0.5) - (b_hh2 - 2 / s) * 2 * c) - bpob * (sq_bpob * (6 + lambda * (22 + lambda * (36 + lambda * 24))) - bppob * (12 + 6 * mu)) - bppob * b_hh2 * 3 * otlambda - b_hh3 * bpob * 4 * otlambda);
          } else
            ds = nu * householder_factor(nu, hh2, hh3);
        }
        // Never leave the branch (or bracket)
        s = take_step(s_left, s_right, s, ds);
      }
      return implied_volatility_output(iterations, s);
    } else {
      const double v_l = normalised_vega(x, s_l), r_lm = convex_rational_cubic_control_parameter_to_fit_second_derivative_at_right_side(b_l, b_c, s_l, s_c, 1 / v_l, 1 / v_c, 0.0, false);
      s = rational_cubic_interpolation(beta, b_l, b_c, s_l, s_c, 1 / v_l, 1 / v_c, r_lm);
      s_left = s_l;
      s_right = s_c;
    }
  } else {
    const double s_u = v_c > DBL_MIN ? s_c + (b_max - b_c) / v_c : s_c, b_u = normalised_black_call(x, s_u);
    if (beta <= b_u) {
      const double v_u = normalised_vega(x, s_u), r_um = convex_rational_cubic_control_parameter_to_fit_second_derivative_at_left_side(b_c, b_u, s_c, s_u, 1 / v_c, 1 / v_u, 0.0, false);
      s = rational_cubic_interpolation(beta, b_c, b_u, s_c, s_u, 1 / v_c, 1 / v_u, r_um);
      s_left = s_c;
      s_right = s_u;
    } else { // The target value beta ϵ [b_u,bₘₐₓ).
      double f_upper_map_h, d_f_upper_map_h_d_beta, d2_f_upper_map_h_d_beta2;
      compute_f_upper_map_and_first_two_derivatives(x, s_u, f_upper_map_h, d_f_upper_map_h_d_beta, d2_f_upper_map_h_d_beta2);
      if (d2_f_upper_map_h_d_beta2 > -SQRT_DBL_MAX && d2_f_upper_map_h_d_beta2 < SQRT_DBL_MAX) {
        const double r_uu = convex_rational_cubic_control_parameter_to_fit_second_derivative_at_left_side(b_u, b_max, f_upper_map_h, 0., d_f_upper_map_h_d_beta, -0.5, d2_f_upper_map_h_d_beta2, true);
        f = rational_cubic_interpolation(beta, b_u, b_max, f_upper_map_h, 0., d_f_upper_map_h_d_beta, -0.5, r_uu);
      }
      if (f <= 0) {
        const double h = b_max - b_u, t = (beta - b_u) / h;
        f = (f_upper_map_h * (1 - t) + 0.5 * h * t) * (1 - t); // We switch to quadratic interpolation using f(b_u), f(b_max)≡0, and f'(b_max)≡-1/2 to specify the quadratic.
      }
      s = inverse_f_upper_map(f);
      s_left = s_u;
      if (beta > 0.5 * b_max) { // Else we better drop through and let the objective function be g(s) = b(x,s)-beta. 
        //
        // In this branch, which comprises the upper segment, the objective function is
        //     g(s) = ln(bₘₐₓ-𝛽)-ln(bₘₐₓ-b(x,s))
        //          ≡ ln((bₘₐₓ-𝛽)/(bₘₐₓ-b(s)))
        // This makes
        //              g'         =   b'/(bₘₐₓ-b)
        // 
        // from here on (see further down), using
        // 
        //           b̄(x,s)       :=   bₘₐₓ   -  b(x,s)
        // and
        //           β̄            :=   bₘₐₓ   -  𝛽
        //
        // we get for ν=-g/g', h₂=g''/g', h₃=g'''/g', h₄=g''''/g' :
        //
        //         ν   =  -g/g'     =   ln(b̄/β̄)·b̄/b'
        //         h₂  =  g''/g'    =   b''/b'   +  b'/b̄
        //                          =   b''/b'   +  g'
        //         h₃  =  g'''/g'   =   b'''/b'  +  g'·(2g'+3b''/b')
        //         h₄  =  g''''/g'  =   b''''/b' +  g'²·6·(g'+2b''/b') + 3·(b''/b')²·g' + 4·(b'''/b')·g'
        //             =  g''''/g'  =   b''''/b' +  g' · ( 6·g'·(g'+2b''/b') + 3·(b''/b')² + 4·(b'''/b') )
        // 
        // and the iteration is
        //     s_n+1  =  s_n  +  ν · ( 1 + ν·h₂/2 ) / ( 1 + ν·( h₂ + ν·h₃/6 ) ).
        //
        const double beta_bar = b_max - beta;
        for (; iterations<N && fabs(ds)>DBL_EPSILON * s; ++iterations) {
#if defined (ENABLE_CHANGING_THE_MAXIMUM_ITERATION_COUNT)
          if (ds * ds_previous < 0)
            ++direction_reversal_count;
          if (N > 3 && iterations > 0 && (3 == direction_reversal_count || !(s > s_left && s < s_right))) {
            // If looping inefficently, or the forecast step takes us outside the bracket, or onto its edges, switch to binary nesting.
            // NOTE that this can only really happen for very extreme values of |x|, such as |x| = |ln(F/K)| > 500.
#ifdef LOG_BINARY_NESTING
            if (direction_reversal_count > 2)
              printf("Intercepting excessive direction reversal in highest branch.\n");
            else
              printf("Intercepting bracket boundary contact/violation in highest branch.\n");
#endif
            s = 0.5 * (s_left + s_right);
            if (s_right - s_left <= DBL_EPSILON * s) break;
            direction_reversal_count = 0;
            ds = 0;
          }
          ds_previous = ds;
          // See below as to the reason behind and the derivation of the formula for b̄(x,s).
          const double h = x / s, t = s / 2, gp /* = bp / b_bar */ = (2 / SQRT_TWO_PI) / (erfcx_cody((t + h) * (1 / SQRT_TWO)) + erfcx_cody((t - h) * (1 / SQRT_TWO))), bp = normalised_vega(x, s), b_bar = bp / gp;
          // b > 𝛽  <=>  b̄ < β̄ and vice versa.
          if (b_bar < beta_bar && s < s_right) s_right = s; else if (b_bar > beta_bar && s > s_left) s_left = s; // Tighten the bracket if applicable.
          if (!(b_bar > DBL_MIN && bp > DBL_MIN)) { // Numerical over-/underflow. Switch to binary nesting for this iteration.
            // NOTE (2023-12-12): since the switch to the direct computation of b̄(x,s) without any subtractive cancellation, I have no longer seen this branch entered into.
#ifdef LOG_BINARY_NESTING
            printf("Binary nesting in highest branch.\n");
#endif
            ds = 0.5 * (s_left + s_right) - s;
          } else
#else
          // See below as to the reason behind and the derivation of the formula for b̄(x,s).
          const double h = x / s, t = s / 2, gp /* = bp / b_bar */ = (2 / SQRT_TWO_PI) / (erfcx_cody((t + h) * (1 / SQRT_TWO)) + erfcx_cody((t - h) * (1 / SQRT_TWO))), b_bar = normalised_vega(x, s) / gp;
#endif
          {
            //
            // Introduced on 2023-12-10
            //
            //    b̄(x,s)            :=   bₘₐₓ   -  b(x,s)
            //    b̄(x,s)             =   eˣ𝄍²  -  [ eˣ𝄍²·Φ(x/s+s/2) - e⁻ˣ𝄍²·Φ(x/s-s/2) ]                     |     using  bₘₐₓ = eˣ𝄍²
            //    b̄(x,s)             =   eˣ𝄍²·Φ(-x/s-s/2)  +  e⁻ˣ𝄍²·Φ(x/s-s/2)                       (1)     |     using  1-Φ(z) = Φ(-z)
            // 
            // Note: no subtractive cancellation!
            // 
            //    b̄(x,s)             =   ½ · [ erfc((s/2+x/s)/√2)·bₘₐₓ + erfc((s/2-x/s)/√2)/bₘₐₓ ]   (2)     |     using  Φ(z) = erfc(-z/√2)/2
            // 
            // In this upper segment, b > bᵤ = b(su), sᵤ = sc + b̄(sc)/b'(sc)   with sc = √(2|x|) and dropping the dependency on x, we benefit from 
            // the [re-]evaluation of (bₘₐₓ-b) via formula (1) or (2) above.
            // 
            // ················································································································································································································
            // To see this, consider that bᵤ(-|x|)/bₘₐₓ is monotonically increasing on |x| ∈ [0,∞). The bounds can be readily computed as follows, assuming w.l.o.g. that x<0:
            //
            //     sᵤ(x)   =   sc + b̄(x,sc)/b'(sc)
            //             =   sc + [ eˣ𝄍²·Φ(-x/sc-sc/2)  +  e⁻ˣ𝄍²·Φ(x/sc-sc/2) ] · exp(½·((x/sc)²+(sc/2)²) · √(2π)               |   x = - √(|x|·|x|), x/sc = - √(|x|/2), sc/2 = +√(|x|/2), x/sc+sc/2 = 0, x/sc-sc/2 = -sc
            //             =   √(2|x|) + [ ½·eˣ𝄍²  +  e⁻ˣ𝄍²·Φ(-√(2|x|)) ] · exp(½·|x|) · √(2π)
            //             =   √(2|x|)  +  √(π/2)  +  e⁻ˣ·Φ(-√(2|x|)) · √(2π)
            //
            // Limiting cases:
            //
            //     sᵤ(0)   =   √(2π)
            //     bᵤ(0)   =   b(0,sᵤ(0))   =   Φ(sᵤ(0)/2)  -  Φ(-sᵤ(0)/2)
            //             =   Φ(√(π/2))  -  Φ(-√(π/2))
            //             =   0.7899085945560624
            // 
            //  x ⟶ -∞:
            // 
            //     sᵤ(x)   =   √(2|x|)  +  √(π/2)  +  e⁻ˣ·Φ(-√(2|x|)) · √(2π)
            //     sᵤ(x)   ≈   √(2|x|)  +  √(π/2)  +  e⁻ˣ·φ(-√(2|x|)) · √(2π) / √(2|x|)                                    | Abramowitz & Stegun 26.2.12
            //             =   √(2|x|)  +  √(π/2)  +  e⁻ˣ·exp(-|x|) / √(2|x|)
            //             =   √(2|x|)  +  √(π/2)  +  1 / √(2|x|)
            //             =   √(2|x|) · ( 1  +  √(π/(4|x|)) +  1/(4|x|) )
            //   x/sᵤ(x)   =   -√(|x|/2) · ( 1  -  √(π/(4|x|)) +  O(1/|x|) )
            //     bᵤ(x)   =   b(x,sᵤ(x))
            //             ≈   eˣ𝄍²·Φ( -√(|x|/2)·(1-√(π/(4|x|))) + √(|x|/2)·(1+√(π/(4|x|))) )    e⁻ˣ𝄍²·Φ( -√(|x|/2)·(1-√(π/(4|x|))) - √(|x|/2)·(1+√(π/(4|x|))) )
            //             =   eˣ𝄍²·Φ( √(π/2) )  -  e⁻ˣ𝄍²·Φ( -√(2|x|) )
            //             =   eˣ𝄍²·Φ( √(π/2) )  -  1/√(4π|x|)                                                             | Abramowitz & Stegun 26.2.12
            // 
            // With bₘₐₓ(x) = eˣ𝄍², this means
            // 
            //    bᵤ(0)/bₘₐₓ(0)   =   Φ(√(π/2))  -  Φ(-√(π/2))   =   0.7899085945560624
            // 
            // and
            //      lim  bᵤ(x)/bₘₐₓ(x)      =      Φ(√(π/2))     =   0.8949542972780312
            //       x→-∞
            // 
            // In other words, on s ∈ [sᵤ,∞), where b  ∈ [bᵤ,bₘₐₓ)  [ 0 < bᵤ ≤ b < bₘₐₓ ], we always have b ≥ bᵤ > ¾·bₘₐₓ and thus b̄ = bₘₐₓ-b < bₘₐₓ/4.
            // And whenever any f̄ = fₘₐₓ-f is less than f/4 we incur less roundoff error in f̄ if we can compute f̄ directly without subtractive cancellation. □ (q.e.d.)
            // ················································································································································································································
            //
            // Continuing from equation (2), using erfc(z) = erfcx(z)·exp(-z²), we get
            // 
            //    b̄(x,s)    =   ½ · ( erfcx((s/2+x/s)/√2)·exp(-½((x/s)²+x+(s/2)²))·eˣ𝄍² + erfcx((s/2-x/s)/√2)·exp(-½((x/s)²-x+(s/2)²))·e⁻ˣ𝄍² )
            //
            //              =   ½ · ( erfcx((s/2+x/s)/√2) + erfcx((s/2-x/s)/√2) ) · exp(-½((x/s)²+(s/2)²))
            //
            //              =   √(π/2) · [ erfcx((s/2+x/s)/√2) + erfcx((s/2-x/s)/√2) ] · ∂b(x,s)/∂s
            //
            // Ergo, ∂b(x,s)/∂s / b̄(x,s)  =  √(2/π) / ( erfcx((s/2+x/s)/√2) + erfcx((s/2-x/s)/√2) )
            //
            const double g = log(beta_bar / b_bar), x_sqr_over_s_cube = (h * h) / s, b_hh2 = x_sqr_over_s_cube - s / 4, c = 3 * square(h / s), b_hh3 = b_hh2 * b_hh2 - c - 0.25;
            const double nu = -g / gp, hh2 = b_hh2 + gp, hh3 = b_hh3 + gp * (2 * gp + 3 * b_hh2);
            //
            // Introduced on 2023-12-14: for very large moneyness ratios [of no commercial relevance: exp(-580) = 1.286E-252], with exactly two Householder(3) iterations, I noticed that there is systematically a
            // residual inaccuracy in this branch (bᵤ ≤ b < bₘₐₓ = eˣ𝄍²) higher than the theoretically attainable one given by (|b(s)/(s·b'(s))|+1)·ε where ε is DBL_EPSILON and b(s) is the normalised Black function.
            // This residual inaccuracy disappears when we use two Householder(4) [5th order accuracy] iterations instead. Tests show that the initial guess is always close enough for the method to be contractive.
            // See further down in the description of the BlackAccuracyFactor() for a derivation of the formula (|b(s)/(s·b'(s))|+1)·ε.
            // 
            if (x < -580) {
              //  b_h₄   =    b''''/b'   =   b_h₂·(b_h₃-½) - (b_h₂-2/s)·6·x²/s⁴
              //   h₄    =    b''''/b' +  g' · ( 6·g'·(g'+2b''/b') + 3·(b''/b')² + 4·(b'''/b') )   =   b_h₄ +  g' · ( 6·g'·(g'+2·b_h₂) + 3·b_h₂² + 4·b_h₃ )
              ds = nu * householder_factor(nu, hh2, hh3, (b_hh2 * (b_hh3 - 0.5) - (b_hh2 - 2 / s) * 2 * c) + gp * (6 * gp * (gp + 2 * b_hh2) + 3 * b_hh2 * b_hh2 + 4 * b_hh3));
            } else
              ds = nu * householder_factor(nu, hh2, hh3);
          }
          // Never leave the branch (or bracket)
          s = take_step(s_left, s_right, s, ds);
        }
        return implied_volatility_output(iterations, s);
      }
    }
  }
  // In this branch, which comprises the two middle segments, the objective function is g(s) = b(x,s)-𝛽, or g(s) = b(s) - 𝛽, for short.
  // This makes
  //              ν    =   -g/g'     =  -(b-𝛽)/b'
  //              h₂   =   g''/g'    =    b''/b'      =   x²/s³-s/4
  //              h₃   =   g'''/g'   =    b'''/b'     =   h₂² - 3·x²/s⁴ - 1/4
  //              h₄   =   g''''/g'  =    b''''/b'    =   h₂·(h₃-½)-(h₂-2/s)·6·x²/s⁴     [ not actually used in this branch ]
  // 
  // and the iteration is
  //     s_n+1  =  s_n  +  ν · ( 1 + ν·h₂/2 ) / ( 1 + ν·( h₂ + ν·h₃/6 ) ).
  //
  for (; iterations<N && fabs(ds)>DBL_EPSILON * s; ++iterations) {
#if defined (ENABLE_CHANGING_THE_MAXIMUM_ITERATION_COUNT)
    if (ds * ds_previous < 0)
      ++direction_reversal_count;
    if (N > 3 && iterations > 0 && (3 == direction_reversal_count || !(s > s_left && s < s_right))) {
      // If looping inefficently, or the forecast step takes us outside the bracket, or onto its edges, switch to binary nesting.
      // NOTE that this can only really happen for very extreme values of |x|, such as |x| = |ln(F/K)| > 500.
#ifdef LOG_BINARY_NESTING
      if (direction_reversal_count > 2)
        printf("Intercepting excessive direction reversal in highest branch.\n");
      else
        printf("Intercepting bracket boundary contact/violation in highest branch.\n");
#endif
      s = 0.5 * (s_left + s_right);
      if (s_right - s_left <= DBL_EPSILON * s) break;
      direction_reversal_count = 0;
      ds = 0;
    }
    ds_previous = ds;
#endif
    const double b = normalised_black_call(x, s), bp = normalised_vega(x, s), nu = (beta - b) / bp, h = x / s, hh2 = (h * h) / s - s / 4, hh3 = hh2 * hh2 - 3 * square(h / s) - 0.25;
#if defined (ENABLE_CHANGING_THE_MAXIMUM_ITERATION_COUNT)
    if (b > beta && s < s_right) s_right = s; else if (b<beta && s>s_left) s_left = s; // Tighten the bracket if applicable.
#endif
    ds = nu * householder_factor(nu, hh2, hh3);
    // Never leave the branch (or bracket)
    s = take_step(s_left, s_right, s, ds);
  }
  return implied_volatility_output(iterations, s);
}

double implied_volatility_from_a_transformed_rational_guess_with_limited_iterations(double price, double F, double K, double T, double q /* q=±1 */, int N) {
  const double intrinsic = fabs(std::max((q < 0 ? K - F : F - K), 0.0));
  if (price < intrinsic)
    return implied_volatility_output(0, VOLATILITY_VALUE_TO_SIGNAL_PRICE_IS_BELOW_INTRINSIC);
  const double max_price = (q < 0 ? K : F);
  if (price >= max_price)
    return implied_volatility_output(0, VOLATILITY_VALUE_TO_SIGNAL_PRICE_IS_ABOVE_MAXIMUM);
  const double x = log(F / K);
  // Map in-the-money to out-of-the-money
  if (q * x > 0) {
    price = fabs(std::max(price - intrinsic, 0.0));
    q = -q;
  }
  return unchecked_normalised_implied_volatility_from_a_transformed_rational_guess_with_limited_iterations(price / (sqrt(F) * sqrt(K)), x, q, N) / sqrt(T);
}

//    b̄(x,s,θ)          :=   bₘₐₓ(x,θ)   -  b(x,s,θ)
//                       =   exp(θ·x/2)  -  θ·[ eˣ𝄍²·Φ(θ·(x/s+s/2)) - e⁻ˣ𝄍²·Φ(θ·(x/s-s/2)) ]                |     using  bₘₐₓ = exp(θ·x/2)
//
//                           ⎧   eˣ𝄍²·[1-Φ(x/s+s/2)] + e⁻ˣ𝄍²·Φ(x/s-s/2)                                     |     when θ = +1
//                       =   ⎨ 
//                           ⎩   eˣ𝄍²·Φ(-x/s-s/2)    + e⁻ˣ𝄍²·[1-Φ(-x/s+s/2)]                                |     when θ = -1
// 
//                       =   eˣ𝄍²·Φ(-x/s-s/2) + e⁻ˣ𝄍²·Φ(x/s-s/2)                                            |     for both θ = ±1
// 
double ComplementaryNormalisedBlack(double x, double s) { return complementary_normalised_black(x / s, s / 2); }

double normalised_implied_volatility_from_a_transformed_rational_guess_with_limited_iterations(double beta, double x, double q /* q=±1 */, int N) {
  // Map in-the-money to out-of-the-money
  if (q * x > 0) {
    beta -= normalised_intrinsic(x, q);
    q = -q;
  }
  if (beta < 0)
    return implied_volatility_output(0, VOLATILITY_VALUE_TO_SIGNAL_PRICE_IS_BELOW_INTRINSIC);
  return unchecked_normalised_implied_volatility_from_a_transformed_rational_guess_with_limited_iterations(beta, x, q, N);
}

double ImpliedBlackVolatility(double price, double F, double K, double T, double q /* q=±1 */) {
  return implied_volatility_from_a_transformed_rational_guess_with_limited_iterations(price, F, K, T, q, IMPLIED_VOLATILITY_MAXIMUM_ITERATIONS);
}

double NormalisedImpliedBlackVolatility(double beta, double x, double q /* q=±1 */) {
  return normalised_implied_volatility_from_a_transformed_rational_guess_with_limited_iterations(beta, x, q, IMPLIED_VOLATILITY_MAXIMUM_ITERATIONS);
}

double Vega(double F, double K, double sigma, double T) { return (sqrt(F) * sqrt(K)) * normalised_vega(log(F / K), sigma * sqrt(T)) * sqrt(T); }

double NormalisedVega(double x, double s) { return normalised_vega(x, s); }

double Volga(double F, double K, double sigma, double T) { return (sqrt(F) * sqrt(K)) * normalised_volga(log(F / K), sigma * sqrt(T)) * T; }

double NormalisedVolga(double x, double s) { return normalised_volga(x, s); }

double DblEpsilon() { return DBL_EPSILON; }

double DblMin() { return DBL_MIN; }

double DblMax() { return DBL_MAX; }

// Floating point numbers have finite precision. The resolution limit is defined as the smallest positive number ε such that 1 and 1+ε still have distinct representations
// in the respectively used floating point model. For standard IEEE 754 double precision (64 bit, 53 bit mantissa), that's about 2.22E-16 and defined as DBL_EPSILON in C/C++.
// We thus have to always assume that any input x into any function f() comes as a number that is representative for some number in the range (x-ε·x,x+ε·x). We will denote
// the concept of 'some number in the range (x-δx,x+δx)' as x±δx.
// 
// Error propagation in generic function evaluation.
// =================================================
//    Given an input number x with associated absolute precision δx, the evaluation of a function f(x) will incur both the uncertainty in the input as well as the finite
// precision of the representation of the result of the evaluation. In other words, instead of y = f(x), by propagation as well as incurred evaluation imprecision, we have
//    y±δy = f(x±δx)·(1±ε)
// which is to lowest order
//         = f(x) ± f'(x)·δx ± f(x)·ε
// Given that the two uncertainty terms on the right hand side can accumulate, net, using y = f(x) as the target (infinite precision) result, this means 
//    |δy| = |f'(x)·δx| + |f(x)·ε|
// which brings us to the *relative* precision of y as
//    |δy/y| = |f'(x)·δx/f(x)| + ε
// IF the input precision on x was |δx| = |x|·ε, we arrive at
//    |δy/y| = ( |x·f'(x)/f(x)| + 1 ) · ε.
// 
// Error propagation in inverse function evaluation.
// =================================================
// Given a function g(y) that is the inverse of another function f(·) such that g(f(x)) = x [in perfect arithmetic], we obtain from y = f(x) and x = g(y) via the same
// logic as above
//    |δx/x|  =  ( |y·g'(y)/g(y)| + 1 ) · ε   =  ( |f(x)/(x·f'(x))| + 1 ) · ε.
// In other words, if the evaluation of y := f(x) incurs a precision deterioration given by the multiplicative factor ( 1 + γ ) [where γ>0], i.e., if the input (relative) precision in x
// was ε and the output (relative) precision in y was (1+γ)·ε, then the evaluation of x := f⁻¹(y) results in the (relative) precision worsening from η := |δy/y| to |δx/x| = (1+1/γ)·η.
// 
// Error propagation in inverse functions with offset.
// ===================================================
// Consider a function f(x) limited from above by its x→∞ asymptotic value fₘₐₓ. Consider that we have, at least in theory, access to the [infinite precision] complementary
// function f̄(x) := fₘₐₓ - f(x). Naturally, we have f̄(x)→0 for x → ∞ , though an inverse of f̄(x) can be very well defined numerically just as the inverse of exp(-x) is well
// defined as x = -ln(y) for y = exp(-x). Having clarified the above, we now in fact seek the inverse of f(x) which obviously satisfies f(x) = fₘₐₓ - f̄(x). In support of
// finding the inverse of y = f(x), we define ȳ := fₘₐₓ - y and the inverse of f̄ as ̄ḡ(·) = f̄⁻¹(·) which is evaluated from any input value y as x := ḡ(fₘₐₓ-y). Note that we
// need to pay attention that the evaluation ȳ = ȳ(y) = fₘₐₓ - y incurs itself from any input value y±δy the error propagation
//     ȳ±δȳ  =  (fₘₐₓ-(y±δy))·(1±ε)  =  (fₘₐₓ-y) ± δy ± (fₘₐₓ-y)·ε ± δy·ε.
// Setting |δy| = |y|·ε since y is an input value, and using ȳ=fₘₐₓ-y gives us (recall that we must alas always accumulate errors in absolute value) to lowest order in ε
//     |δȳ|  =  (|y|+|ȳ|)·ε ,
// i.e.,
//     |δȳ/ȳ|  =  (1+|y/ȳ|)·ε .
// We now compute the error propagation of the inverse function evaluation ḡ(ȳ) with ȳ=(fₘₐₓ-y) from the input y±δy with |δy| = |y|·ε to lowest order in ε as follows:
//     x±δx  =  ḡ(ȳ±δȳ)·(1±ε)
//           =  ḡ(ȳ±(|y|+|ȳ|)·ε)·(1±ε)
//           =  ḡ(ȳ) ± ḡ'(ȳ)·(|y|+|ȳ|)·ε ± ḡ(ȳ)·ε
// Since ḡ(ȳ)=x, this yields
//     |δx|  =  [ |ḡ'(ȳ)|·(|y|+|ȳ|) + |x| ] · ε.
// Using ḡ'(ȳ) = 1/f̄'(x) and |f̄'(x)| = |f'(x)|, we continue
//     |δx|  =  [ (|y|+|ȳ|)/|f'(x)| + |x| ] · ε
// whence
//   |δx/x|  =  [ |f(x)|/|x·f'(x)|·(1+|fₘₐₓ/f(x)-1|) + 1 ] · ε .
// For x → ∞, we have f(x) → fₘₐₓ which brings us back to
//   |δx/x|  ≈  [ |f(x)|/|x·f'(x)| + 1 ] · ε
// despite the fact that the *relative* accuracy of the complementary value ȳ = f̄(x) diverges according to |δȳ/ȳ|  =  (1+|y/ȳ|)·ε when ȳ → 0 in the limit of x → ∞.
// 
// The attainable *relative* accuracy of 𝛽 = b(s) when s has *relative* accuracy ε is (to lowest order) (|s·b'(s)/b(x)|+1)·ε --- see the source code for a detailed derivation.
// The attainable *relative* accuracy of x = b⁻¹(𝛽) when 𝛽 has *relative* accuracy ε is (to lowest order) (|b(s)/(s·b'(s))|+1)·ε .
// This function returns (s·∂b(x,s)/∂s)/b(x,s,θ=±1). In order to get the accuracy limit of implied volatility calculations, take (1+1/NormalisedBlackAccuracyFactor(x,s,θ))·DBL_EPSILON.
double BlackAccuracyFactor(double x, double s, double theta /* theta=±1 */) { return s / std::get<0>(normalised_black_call_over_vega_and_ln_vega(theta < 0 ? -x : x, s)); }

double ImpliedVolatilityAttainableAccuracy(double x, double s, double theta /* theta=±1 */) {
  // Structured bindings trigger a waning about the need for -std=c++17 with some older versions of g++. I don't like the tuple syntax: I very much prefer structured binding syntax, but I dislike warnings even more.
#if __cplusplus >= 201703L
  const auto [bx, ln_vega] = normalised_black_call_over_vega_and_ln_vega(theta < 0 ? -x : x, s);
#else
  const auto bx_and_ln_vega = normalised_black_call_over_vega_and_ln_vega(theta < 0 ? -x : x, s);
  const double bx = std::get<0>(bx_and_ln_vega), ln_vega = std::get<1>(bx_and_ln_vega);
#endif
  const double b = bx * exp(ln_vega), b_max = exp((theta < 0 ? -x : x) / 2);
  return (b > DBL_MIN && b < b_max) ? DBL_EPSILON * (1 + fabs(bx / s)) : 1;
}

#if !defined(NO_XL_API)

# include "XLFunctions.h"

// "" maps to the C name of the function, "." maps to <XL-Category>.<C-function-name>.
DECLARE_XL_FUNCTION(Black, { "","." }, "BBBBBB$", "F,K,sigma,T,q", "The Black [1976] option value Black(F,K,sigma,T,q).", { "the Forward.", "the Strike.", "the volatility.", "the time to expiry.", "q=+/-1 for calls/puts." });

DECLARE_XL_FUNCTION(NormalisedBlack, { "","." }, "BBBB$", "x,s,q",
                    "The normalised Black call option value [exp(x/2)·Phi(x/s+s/2)-exp(-x/2)·Phi(x/s-s/2)] with x=ln(F/K) and s=sigma·sqrt(T).",
                    { "x=ln(F/K)", "s=sigma·sqrt(T).", "q=+/-1 for calls/puts." });

DECLARE_XL_FUNCTION(ImpliedBlackVolatility, { "",".","ImpliedVolatility",".ImpliedVolatility" }, "BBBBBB$", "price,F,K,T,q",
                    "The implied volatility sigma such that the given price equals the Black option value [F·Phi(q·(x/s+s/2))-K·Phi(q·(x/s-s/2))] with x=ln(F/K) and s=sigma·sqrt(T).",
                    { "price=Black(F,K,sigma,T,q)", "the Forward.", "the Strike.", "the time to expiry.", "q=+/-1 for calls/puts." });

extern "C" DLL_EXPORT double NormalisedImpliedBlackVolatilityForExcel(double beta, double x, double q /* q=±1 */,const XLOper&xlN) {
  return normalised_implied_volatility_from_a_transformed_rational_guess_with_limited_iterations(beta, x, q, xlN.isUndefined() ? IMPLIED_VOLATILITY_MAXIMUM_ITERATIONS : xlN.to_int());
}

DECLARE_XL_FUNCTION(NormalisedImpliedBlackVolatilityForExcel, { "NormalisedImpliedBlackVolatility",".NormalisedImpliedBlackVolatility","NormalisedImpliedVolatility",".NormalisedImpliedVolatility" }, "BBBB?$", "normalised_price,x,q,[n]",
                    "The normalised implied volatility s such that the given normalised price equals the normalised Black option value [exp(x/2)·Phi(q·(x/s+s/2))-exp(-x/2)·Phi(q·(x/s-s/2))] with x=ln(F/K) and s=sigma·sqrt(T).",
                    { "normalised_price=Black(F,K,sigma,T,q)/sqrt(F·K)", "x=ln(F/K).", "q=+/-1 for calls/puts.", "the number of iterations, e.g., 0 gives you the initial guess in \"Let's Be Rational\". Omit if you want to allow for the default number (usually 2)." });

DECLARE_XL_FUNCTION(norm_cdf, { "CumNorm",".CumNorm" }, "BB$", "x",
                    "The cumulative normal distribution for the given argument x.",
                    { "the argument." });

DECLARE_XL_FUNCTION(inverse_norm_cdf, { "InvCumNorm",".InvCumNorm" }, "BB$", "p",
                    "The inverse cumulative normal distribution for the given probability p.",
                    { "the probability." });

DECLARE_XL_FUNCTION(Vega, { "","." }, "BBBBB$", "F,K,σ,T", "The Black [1976] option value sensitivity ∂Black(F,K,σ,T)/∂σ.", { "the Forward.", "the Strike.", "the volatility.", "the time to expiry." });

DECLARE_XL_FUNCTION(NormalisedVega, { "","." }, "BBB$", "x,s", "The normalised Black option value sensitivity ∂b(x,s)/∂s.", { "x=ln(F/K)", "s=σ·√T." });

DECLARE_XL_FUNCTION(Volga, { "","." }, "BBBBB$", "F,K,σ,T", "The Black [1976] option value sensitivity ∂²Black(F,K,σ,T)/∂σ².", { "the Forward.", "the Strike.", "the volatility.", "the time to expiry." });

DECLARE_XL_FUNCTION(NormalisedVolga, { "","." }, "BBB$", "x,s", "The normalised Black option value sensitivity ∂²b(x,s)/∂s².", { "x=ln(F/K)", "s=σ·√T." });

DECLARE_XL_FUNCTION(DblEpsilon, { "","." }, "B$", "", "Returns DBL_EPSILON.", { });

DECLARE_XL_FUNCTION(DblMin, { "","." }, "B$", "", "Returns DBL_MIN.", { });

DECLARE_XL_FUNCTION(DblMax, { "","." }, "B$", "", "Returns DBL_MAX.", { });

DECLARE_XL_FUNCTION(ComplementaryNormalisedBlack, { "." }, "BBB$", "x,s",
                    "The complementary normalised Black option value b̄(x,s) = bₘₐₓ(x,theta) - b(x,s,theta) = exp(½x)·Φ(-x/s-s/2) + exp(-½x)·Φ(x/s-s/2) with x=ln(F/K) and s=sigma·sqrt(T), where b_max = exp(theta·x/2). The dependency on theta cancels out.",
                    { "x=ln(F/K)", "s=sigma·sqrt(T)." });

DECLARE_XL_FUNCTION(ImpliedVolatilityAttainableAccuracy, { ".ImpliedVolatilityAttainableAccuracy",".ImpliedBlackVolatilityAttainableAccuracy" }, "BBBB$", "x,s,q",
                    "The theoretically attainable accuracy of implied volatility according to error propagation analysis (1st order):  (|b(s)/(s·b'(s))|+1)·ε  where ε = DBL_EPSILON.",
                    { "x=ln(F/K).", "q=+/-1 for calls/puts." });

# ifdef ENABLE_CHANGING_THE_MAXIMUM_ITERATION_COUNT
DECLARE_XL_FUNCTION(set_implied_volatility_maximum_iterations, ".", "JJ$", "n", "Sets and returns the maximum number of iterations in implied volatility calculations. Negative inputs leave the status unchanged (use for enquiry).", { "the requested maximum number." });
# endif

# ifdef ENABLE_CHANGING_THE_HOUSEHOLDER_METHOD_ORDER
DECLARE_XL_FUNCTION(set_implied_volatility_householder_method_order, ".", "JJ$", "order", "Sets and returns the Householder method order in implied volatility calculations. Negative inputs leave the status unchanged (use for enquiry).", { "the requested order: 2[=Newton], 3[=Halley], or 4[=Householder(3)]." });
# endif

# ifdef ENABLE_SWITCHING_THE_OUTPUT_TO_ITERATION_COUNT
DECLARE_XL_FUNCTION(set_implied_volatility_output_type, ".", "JJ$", "type", "Sets and returns the output value of implied volatility function invocations. When 0, those functions returned the [normalised] implied volatility, else the iteration count [divided by sqrt(T) unless normalised].", { "the requested output type: 0 or 1." });
# endif

#endif // !defined(NO_XL_API)
