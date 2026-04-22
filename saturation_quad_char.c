/*
 * FORMAL VERIFICATION: QUADRATIC CHARACTERIZATION of the UNIT SATURATION FUNCTION
 *
 * Constraints: 5 quadratic inequalities
 * Subsets: 3
 *
 * Verify: frama-c -wp -wp-prover alt-ergo,z3 saturation_quad_char.c
 */

/* --- 1. Polynomial Coefficients --- */
/* Constants extracted the certified Sum-of-Squares (SOS) quadratic functions */

// Q1
#define Q1_a  (0.0)
#define Q1_b  (-1.0)
#define Q1_c  (0.0)
#define Q1_d  (0.0)
#define Q1_e  (0.0)
#define Q1_f  (1.0)

// Q2
#define Q2_a  (0.0003)
#define Q2_b  (-0.3388)
#define Q2_c  (0.7693)
#define Q2_d  (0.7711)
#define Q2_e  (0.0404)
#define Q2_f  (0.3831)

// Q3
#define Q3_a  (0.4382)
#define Q3_b  (-0.9360)
#define Q3_c  (0.5384)
#define Q3_d  (1.4419)
#define Q3_e  (-1.3690)
#define Q3_f  (0.0338)

// Q4
#define Q4_a  (0.0003)
#define Q4_b  (-0.3388)
#define Q4_c  (0.7693)
#define Q4_d  (-0.7711)
#define Q4_e  (-0.0404)
#define Q4_f  (0.3831)

// Q5
#define Q5_a  (0.4382)
#define Q5_b  (-0.9360)
#define Q5_c  (0.5384)
#define Q5_d  (-1.4419)
#define Q5_e  (1.3690)
#define Q5_f  (0.0338)


/* --- 2. Polynomial Evaluation Functions --- */
/* Logic functions to map variables to the 2D quadratics in continuous real space */

/*@
  logic real eval_Q1(real x, real y) = 
      Q1_a * x * x + Q1_b * y * y + Q1_c * x * y + 
      Q1_d * x + Q1_e * y + Q1_f;
  
  logic real eval_Q2(real x, real y) = 
      Q2_a * x * x + Q2_b * y * y + Q2_c * x * y + 
      Q2_d * x + Q2_e * y + Q2_f;
  
  logic real eval_Q3(real x, real y) = 
      Q3_a * x * x + Q3_b * y * y + Q3_c * x * y + 
      Q3_d * x + Q3_e * y + Q3_f;
  
  logic real eval_Q4(real x, real y) = 
      Q4_a * x * x + Q4_b * y * y + Q4_c * x * y + 
      Q4_d * x + Q4_e * y + Q4_f;
  
  logic real eval_Q5(real x, real y) = 
      Q5_a * x * x + Q5_b * y * y + Q5_c * x * y + 
      Q5_d * x + Q5_e * y + Q5_f;
*/


/* --- 3. Region of Interest (ROI) Definitions --- */
/* Mathematical definitions of the piecewise saturation function subsets*/

/*@ axiomatic ROI_Subsets {
  @
  @ // Subset 1: Left Saturation (y = -1, x <= -1)
  @ predicate in_subset_1(real x, real y);
  @
  @ axiom subset_1_definition:
  @   \forall real x, y;
  @     in_subset_1(x, y) <==>
  @       (y + 1 >= 0.0) &&
  @       (- y - 1 >= 0.0) &&
  @       (- x - 1 >= 0.0);
  @
  @ // Subset 2: Linear Center (y = x, -1 <= x <= 1)
  @ predicate in_subset_2(real x, real y);
  @
  @ axiom subset_2_definition:
  @   \forall real x, y;
  @     in_subset_2(x, y) <==>
  @       (y - x >= 0.0) &&
  @       (x - y >= 0.0) &&
  @       (1 - x >= 0.0) &&
  @       (x + 1 >= 0.0);
  @
  @ // Subset 3: Right Saturation (y = 1, x >= 1)
  @ predicate in_subset_3(real x, real y);
  @
  @ axiom subset_3_definition:
  @   \forall real x, y;
  @     in_subset_3(x, y) <==>
  @       (y - 1 >= 0.0) &&
  @       (1 - y >= 0.0) &&
  @       (x - 1 >= 0.0);
  @
  @ // Full ROI: Union of all three saturation pieces
  @ predicate in_ROI(real x, real y);
  @
  @ axiom ROI_union:
  @   \forall real x, y;
  @     in_ROI(x, y) <==>
  @       in_subset_1(x, y) ||
  @       in_subset_2(x, y) ||
  @       in_subset_3(x, y);
  @ }
*/


/* --- 4. Sub-Goal Verification --- */
/* Lemmas proving each polynomial is strictly non-negative on individual subsets */

/*@ lemma Q1_on_subset_1:
  @ \forall real x, y;
  @   in_subset_1(x, y) ==> eval_Q1(x, y) >= 0;
*/

/*@ lemma Q1_on_subset_2:
  @ \forall real x, y;
  @   in_subset_2(x, y) ==> eval_Q1(x, y) >= 0;
*/

/*@ lemma Q1_on_subset_3:
  @ \forall real x, y;
  @   in_subset_3(x, y) ==> eval_Q1(x, y) >= 0;
*/

/*@ lemma Q2_on_subset_1:
  @ \forall real x, y;
  @   in_subset_1(x, y) ==> eval_Q2(x, y) >= 0;
*/

/*@ lemma Q2_on_subset_2:
  @ \forall real x, y;
  @   in_subset_2(x, y) ==> eval_Q2(x, y) >= 0;
*/

/*@ lemma Q2_on_subset_3:
  @ \forall real x, y;
  @   in_subset_3(x, y) ==> eval_Q2(x, y) >= 0;
*/

/*@ lemma Q3_on_subset_1:
  @ \forall real x, y;
  @   in_subset_1(x, y) ==> eval_Q3(x, y) >= 0;
*/

/*@ lemma Q3_on_subset_2:
  @ \forall real x, y;
  @   in_subset_2(x, y) ==> eval_Q3(x, y) >= 0;
*/

/*@ lemma Q3_on_subset_3:
  @ \forall real x, y;
  @   in_subset_3(x, y) ==> eval_Q3(x, y) >= 0;
*/

/*@ lemma Q4_on_subset_1:
  @ \forall real x, y;
  @   in_subset_1(x, y) ==> eval_Q4(x, y) >= 0;
*/

/*@ lemma Q4_on_subset_2:
  @ \forall real x, y;
  @   in_subset_2(x, y) ==> eval_Q4(x, y) >= 0;
*/

/*@ lemma Q4_on_subset_3:
  @ \forall real x, y;
  @   in_subset_3(x, y) ==> eval_Q4(x, y) >= 0;
*/

/*@ lemma Q5_on_subset_1:
  @ \forall real x, y;
  @   in_subset_1(x, y) ==> eval_Q5(x, y) >= 0;
*/

/*@ lemma Q5_on_subset_2:
  @ \forall real x, y;
  @   in_subset_2(x, y) ==> eval_Q5(x, y) >= 0;
*/

/*@ lemma Q5_on_subset_3:
  @ \forall real x, y;
  @   in_subset_3(x, y) ==> eval_Q5(x, y) >= 0;
*/


/* --- 5. Global Constraint Verification --- */
/* Lemmas extending the non-negativity to the full domain (union of the subsets) */

/*@ lemma Q1_on_ROI:
  @ \forall real x, y;
  @   in_ROI(x, y) ==> eval_Q1(x, y) >= 0;
*/

/*@ lemma Q2_on_ROI:
  @ \forall real x, y;
  @   in_ROI(x, y) ==> eval_Q2(x, y) >= 0;
*/

/*@ lemma Q3_on_ROI:
  @ \forall real x, y;
  @   in_ROI(x, y) ==> eval_Q3(x, y) >= 0;
*/

/*@ lemma Q4_on_ROI:
  @ \forall real x, y;
  @   in_ROI(x, y) ==> eval_Q4(x, y) >= 0;
*/

/*@ lemma Q5_on_ROI:
  @ \forall real x, y;
  @   in_ROI(x, y) ==> eval_Q5(x, y) >= 0;
*/


/* --- 6. Main Sound Over-Approximation --- */
/* Final step: proving the conjunction of all polynomials is a sound over-approximation of the ROI */

/*@ lemma over_approximation:
  @ \forall real x, y;
  @   in_ROI(x, y) ==>
  @     eval_Q1(x, y) >= 0 &&
  @     eval_Q2(x, y) >= 0 &&
  @     eval_Q3(x, y) >= 0 &&
  @     eval_Q4(x, y) >= 0 &&
  @     eval_Q5(x, y) >= 0;
*/

void main(void) {}