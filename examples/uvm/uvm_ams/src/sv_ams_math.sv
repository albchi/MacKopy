//-----------------------------------------------------------------------------
// This confidential and proprietary software may be used only as authorized
// by a licensing agreement from Synopsys Inc. In the event of publication,
// the following notice is applicable:
//
// (C) COPYRIGHT 2013 SYNOPSYS INC.  ALL RIGHTS RESERVED
//
// The entire notice above must be reproduced on all authorized copies.
//-----------------------------------------------------------------------------
//
// Description : Math functions
//
//-----------------------------------------------------------------------------

////////////////////////////////////////////////////////////
`ifndef _SV_AMS_MATH_SV
`define _SV_AMS_MATH_SV

////////////////////////////////////////////////////////////
// Class: sv_ams_const
//    The <sv_ams_const> class provides pre-defined constant that
// are useful for modeling generators and analog behaviors
class sv_ams_const;
  // Const: PI
  static const real PI=3.14159263;
  // Const: HALF_PI
  static const real HALF_PI=PI/2.0;
  // Const: TWO_PI
  static const real TWO_PI=PI*2.0;
endclass

////////////////////////////////////////////////////////////
// Package: sv_ams_math
//
//    The <sv_ams_math> package provides pre-defined C functions
// that are useful for modeling generators and analog behaviors
package sv_ams_math;
  
  // Function: cos
  //   This function returns the cosine of *a*.
  import "DPI-C" function real cos(input real a);
  // Function: cosh
  //   This function returns the hyperbolic cosine of *a*
  import "DPI-C" function real cosh(input real a);
  // Function: acos
  //   This function returns the inverse cosine (arccosine) of *a*.
  import "DPI-C" function real acos(input real a);
  // Function: acosh
  //   This function returns the inverse hyperbolic cosine of *a*
  import "DPI-C" function real acosh(input real a);

  // Function: sin
  //   This function returns the sine of *a*.
  import "DPI-C" function real sin(input real a);
  // Function: sinh
  //   This function Returns the hyperbolic sine of *a*
  import "DPI-C" function real sinh(input real a);
  // Function: asin
  //   This function returns the inverse sine (arcsine) of *a*.
  import "DPI-C" function real asin(input real a);
  // Function: asinh
  //   This function returns the inverse hyperbolic sine of *a*
  import "DPI-C" function real asinh(input real a);

  // Function: tan
  //   This function returns the tangent of *a*
  import "DPI-C" function real tan(input real a);
  // Function: tanh
  //   This function returns the hyperbolic tangent of *a*
  import "DPI-C" function real tanh(input real a);
  // Function: atan
  //   This function returns the inverse tangent (arctangent) of *a*.
  import "DPI-C" function real atan(input real a);
  // Function: atanh
  //   This function returns the inverse hyperbolic tangent of *a*
  import "DPI-C" function real atanh(input real a);
  // Function: atan2
  //   This function retunrs the inverse tangent (arctangent) of the real parts of *a* and *b*
  import "DPI-C" function real atan2(input real a, input real b);

  // Function: exp
  //   This function returns the base-e exponential function of *a*, which is the e number raised to the power *a* ...
  import "DPI-C" function real exp(input real a);
  // Function: expm1
  //   This function returns exp( *a* ) - 1
  import "DPI-C" function real expm1(input real a);
  // Function: log
  //   This function returns the base-e logarithm of *a*
  import "DPI-C" function real log(input real a);
  // Function: log10
  //   This function returns the base-10 logarithm of *a*
  import "DPI-C" function real log10(input real a);
  // Function: ilogb
  //   This function returns an unbiased exponent
  import "DPI-C" function int  ilogb(input real a);
  // Function: log1p
  //   This function returns log_e(1.0 + *a* )
  import "DPI-C" function real log1p(input real a);
  // Function: logb
  //   This function returns radix-independent exponent
  import "DPI-C" function real logb(input real a);

  // Function: fabs
  //   This function returns the absolute value of *a*
  import "DPI-C" function real fabs(input real a);
  // Function: ceil
  //   This function Returns the smallest integral value that is not less than *a*
  import "DPI-C" function real ceil(input real a);
  // Function: floor
  //   This function returns the largest integral value that is not greater than *a*
  import "DPI-C" function real floor(input real a);
  // Function: fmod
  //   This function Returns the floating-point remainder of numerator/denominator (*a* / *b*).
  //   The remainder of a division operation is the result of subtracting the integral quotient multiplied by the denominator from the numerator:
  //     remainder = numerator - quotient * denominator
  import "DPI-C" function real fmod(input real a, input real b);
  // Function: frexp
  //   This function Breaks the floating point number *a* into its binary significand 
  // (a floating point value between 0.5(included) and 1.0(excluded)) and an integral *b* for 2, such that:
  //     *a* = significand * 2 exponent
  // The exponent is stored in the location pointed by *b*, and the significand is the value returned by the function.
  // If *a* is zero, both parts (significand and exponent) are zero.
  import "DPI-C" function real frexp(input real a, input integer b); // ref for 2nd arg
  // Function: ldexp
  //   This function Returns the resulting floating point value from multiplying *a* (the significand) 
  // by 2 raised to the power of *b* (the exponent).
  import "DPI-C" function real ldexp(input real a, input integer b);

  // Function: modf
  //   This function Break into fractional and integral parts
  //   Breaks *a* into two parts: the integer part (stored in the object pointed by *b*) and the fractional part (returned by the function).
  //   Each part has the same sign as *a*.
  import "DPI-C" function real modf(input real a, input real b); // ref for 2nd arg

  // Function: pow
  //   This function returns *a* raised to the power *b*
  import "DPI-C" function real pow(input real a, input real b);
  // Function: sqrt
  //   This function returns the square root of *a*
  import "DPI-C" function real sqrt(input real a);
  // Function: hypot
  //   This function returns the length of the hypotenuse of a right-angled triangle with sides of length
  //   *a* and *b*.
  import "DPI-C" function real hypot(input real a, input real b);

  // Function: erf
  //   This function returns the error function of x; defined as
  //   erf(x) = 2/sqrt(pi)* integral from 0 to x of exp(-t*t) dt
  //   The erfc() function returns the complementary error function of x, that is 1.0 - erf(x).
  import "DPI-C" function real erf(input real a);
  // Function: erfc
  //   This function returns the complementary error function 1.0 - erf(x).
  import "DPI-C" function real erfc(input real a);

  // Function: gamma
  //   This function returns the gamma function of *a*
  import "DPI-C" function real gamma(input real a);
  // Function: lgamma
  //   This function returns the logarithm gamma function of *a*
  import "DPI-C" function real lgamma(input real a);

  // Function: j0
  //   This function returns the relevant Bessel value of x of the first kind of order 0
  import "DPI-C" function real j0(input real a);
  // Function: j1
  //   This function returns the relevant Bessel value of x of the first kind of order 1
  import "DPI-C" function real j1(input real a);
  // Function: jn
  //   This function returns the relevant Bessel value of x of the first kind of order n
  import "DPI-C" function real jn(input int i, input real a);

  // Function: y0
  //   This function returns the relevant Bessel value of x of the second kind of order 0
  import "DPI-C" function real y0(input real a);
  // Function: y1
  //   This function returns the relevant Bessel value of x of the second kind of order 1
  import "DPI-C" function real y1(input real a);
  // Function: yn
  //   This function returns the relevant Bessel value of x of the second kind of order n
  import "DPI-C" function real yn(input int i, input real a);

  // Function: isnan
  //   This function returns a non-zero value if value *a* is "not-a-number" (NaN), and 0 otherwise.
  import "DPI-C" function int  isnan(input real a);

  // Function: cbrt
  //   This function returns the real cube root of their argument *a*.
  import "DPI-C" function real cbrt(input real a);

  // Function: nextafter
  //   This function returns the next representable floating-point value following x in
  //   the direction of y.  Thus, if y is less than x, nextafter() shall return the largest 
  //   representable floating-point number less than x.
  import "DPI-C" function real nextafter(input real a, input real b);

  // Function: remainder
  //   This function returns the floating-point remainder r= *a*- n*y* when *y* is non-zero. The value n is the integral value nearest the
  //   exact value *a*/ *y*.  When |n-*a*/*y*|=0.5, the value n is chosen to be even.
  import "DPI-C" function real remainder(input real a, input real b);

  // Function: rint
  //   This function returns the integral value (represented as a double) nearest *a* in the direction of the current rounding mode
  import "DPI-C" function real rint(input real a);
  // Function: scalb
  //   This function returns  *a* * r** *b*, where r is the radix of the machine floating-point arithmetic
  import "DPI-C" function real scalb(input real a, input real b);
endpackage  
      
////////////////////////////////////////////////////////////
// Class: sv_ams_units
//   This class defines handy enumerated types for voltage, current, frequency and time.
//   It also provides functions that returns scale factor for a given unit.
//
// Example
//|
//| module top;
//|   real r;
//|   sv_ams_real z=new(0.0);
//|   initial begin
//|      r = z.urandom(0,100) * sv_ams_units::get_current_unit(sv_ams_units::uA);
//|   end
//| endmodule
//|

class sv_ams_units;
  import sv_ams_math::*;

  // const: one_kA 
  // Defines scale factor for 1kA
  static const real one_kA = get_current_unit(kA);
  // const: one_A 
  // Defines scale factor for 1A
  static const real one_A  = get_current_unit(A);
  // const: one_mA 
  // Defines scale factor for 1mA
  static const real one_mA = get_current_unit(mA);
  // const: one_uA 
  // Defines scale factor for 1uA
  static const real one_uA = get_current_unit(uA);
  // const: one_nA 
  // Defines scale factor for 1nA
  static const real one_nA = get_current_unit(nA);

  // const: one_kV 
  // Defines scale factor for 1kV
  static const real one_kV = get_voltage_unit(kV);
  // const: one_V 
  // Defines scale factor for 1V
  static const real one_V  = get_voltage_unit(V);
  // const: one_mV 
  // Defines scale factor for 1mV
  static const real one_mV = get_voltage_unit(mV);
  // const: one_uV 
  // Defines scale factor for 1uV
  static const real one_uV = get_voltage_unit(uV);
  // const: one_nV 
  // Defines scale factor for 1nV
  static const real one_nV = get_voltage_unit(nV);

  // const: one_GHz 
  // Defines scale factor for 1GHz
  static const real one_GHz = get_frequency_unit(GHz);
  // const: one_MHz 
  // Defines scale factor for 1MHz
  static const real one_MHz = get_frequency_unit(MHz);
  // const: one_kHz 
  // Defines scale factor for 1kHz
  static const real one_kHz = get_frequency_unit(kHz);
  // const: one_Hz 
  // Defines scale factor for 1Hz
  static const real one_Hz  = get_frequency_unit(Hz);

  // const: one_ns 
  // Defines scale factor for 1ns
  static const real one_ns = get_time_unit(ns);
  // const: one_us 
  // Defines scale factor for 1us
  static const real one_us = get_time_unit(us);
  // const: one_ms 
  // Defines scale factor for 1ms
  static const real one_ms = get_time_unit(ms);
  // const: one_s 
  // Defines scale factor for 1s
  static const real one_s  = get_time_unit(s);

  // Enum: current_e
  // Defines enumerated types for current
  typedef enum int {
                     kA=+3, 
                      A= 0,
                     mA=-3, 
                     uA=-6, 
                     nA=-9
                    } current_e;

  // Enum: voltage_e
  // Defines enumerated types for voltage
  typedef enum int {
                     kV=+3, 
                      V= 0,
                     mV=-3, 
                     uV=-6, 
                     nV=-9
                    } voltage_e;

  // Enum: frequency_e
  // Defines enumerated types for frequency
  typedef enum int {
                     GHz=+9,
                     MHz=+6,
                     kHz=+3,
                      Hz= 0
                    } frequency_e;

  // Enum: time_e
  // Defines enumerated types for time
  typedef enum int {
                     ns=-9,
                     us=-6,
                     ms=-3,
                      s= 0
                    } time_e;

  // Function: get_current_unit
  //   This function returns the scale factor for a given current unit
  static function real get_current_unit(current_e c);
    return pow(10.0,c);
  endfunction

  // Function: get_voltage_unit
  //   This function returns the scale factor for a given voltage unit
  static function real get_voltage_unit(voltage_e v);
    return pow(10.0,v);
  endfunction

  // Function: get_frequency_unit
  //   This function returns the scale factor for a given frequency unit
  static function real get_frequency_unit(frequency_e f);
    return pow(10.0,f);
  endfunction

  // Function: get_time_unit
  //   This function returns the scale factor for a given time unit
  static function real get_time_unit(time_e t);
    return pow(10.0,t);
  endfunction

endclass

`endif
