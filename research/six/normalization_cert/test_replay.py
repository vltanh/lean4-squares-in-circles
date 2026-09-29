"""Arithmetic and fail-closed regression tests for the independent backend.

These tests guard implementation errors; the arithmetic justification is the
integer rounding/Taylor argument in rational_arb_compat.py, not sampling.
"""
from fractions import Fraction as F
from random import Random
import sys
import unittest
import rational_arb_compat as R

sys.modules['flint'] = R
from bnb import bnb
import ia


def contains(box,value):
    value = F(value)
    return F(box.l,R.SCALE)<=value<=F(box.h,R.SCALE)


class ReplayTests(unittest.TestCase):
    def test_rational_arithmetic(self):
        rng = Random(60027)
        for _ in range(250):
            a,b = F(rng.randrange(-1000,1001),rng.randrange(1,1000)),F(rng.randrange(-1000,1001),rng.randrange(1,1000))
            x,y = R.arb(a),R.arb(b)
            self.assertTrue(contains(x+y,a+b))
            self.assertTrue(contains(x-y,a-b))
            self.assertTrue(contains(x*y,a*b))
            self.assertTrue(contains(x**2,a*a))
            if b: self.assertTrue(contains(x/y,a/b))

    def test_interval_products(self):
        x = R.arb(-3).union(R.arb(2))
        y = R.arb(-5).union(R.arb(7))
        self.assertTrue(contains(x*y,-21))
        self.assertTrue(contains(x*y,15))
        self.assertEqual((x**2).l,0)
        self.assertTrue(contains(x**2,9))
        with self.assertRaises(ValueError): x.inv()

    def test_sqrt_brackets(self):
        for q in (F(0),F(1,2),F(2),F(142559,50000)):
            a = R.arb(q).sqrt()
            self.assertLessEqual(F(a.l,R.SCALE)**2,q)
            self.assertGreaterEqual(F(a.h,R.SCALE)**2,q)
        with self.assertRaises(ValueError): R.arb(-1).sqrt()

    def test_trig_critical_points(self):
        p = R.arb.pi()
        self.assertTrue(contains((p/2).sin(),1))
        self.assertTrue(contains((-p/2).sin(),-1))
        self.assertTrue(contains(p.cos(),-1))
        self.assertTrue(contains(R.arb(-2).union(R.arb(2)).sin(),1))
        self.assertTrue(contains(R.arb(-2).union(R.arb(2)).sin(),-1))
        self.assertTrue(contains(R.arb(0).sin(),0))
        self.assertTrue(contains(R.arb(0).cos(),1))
        self.assertEqual(R.arb(-20).union(R.arb(20)).sin().l,-R.SCALE)

    def test_inverse_brackets(self):
        self.assertEqual(R.arb(0).asin().l,0)
        self.assertEqual(R.arb(0).atan().h,0)
        x = R.arb(F(1,3))
        self.assertTrue(contains(x.asin().sin(),F(1,3)))
        self.assertTrue(contains(x.atan().tan(),F(1,3)))

    def test_float_endpoint_cover(self):
        a = ia.iv(1/3,1/3)
        self.assertTrue(contains(a,F(1,3)))
        self.assertTrue(contains(a,F(1/3)))

    def test_bnb_limits_are_not_success(self):
        for depth,budget in ((0,100),(20,1)):
            stats,un,n = bnb([(0.0,1.0)],lambda box:None,[1],max_depth=depth,max_boxes=budget,verbose=False)
            self.assertTrue(un)
            self.assertFalse(stats)
        with self.assertRaises(ValueError): bnb([(0,1)],lambda box:'ok',[0],verbose=False)
        with self.assertRaises(TypeError): bnb([(0,1)],lambda box:True,[1],verbose=False)

    def test_exact_child_cover(self):
        leaves = []
        def ev(box): return 'small' if box[0][1]-box[0][0]<=0.125 else None
        stats,un,n = bnb([(0.0,1.0)],ev,[1],record=lambda box,reason:leaves.append(box[0]),verbose=False)
        self.assertFalse(un)
        leaves.sort()
        self.assertEqual(len(leaves),8)
        self.assertEqual(leaves[0][0],0)
        self.assertEqual(leaves[-1][1],1)
        for left,right in zip(leaves,leaves[1:]): self.assertEqual(left[1],right[0])

    def test_central_boundary_witness(self):
        # On cx=c0 the axis-parallel east square has marker zero and fits.
        # The forbidden-arc predicate's hand exclusions are NOT valid here.
        square = ia.SqBox(R.arb(0),ia.RHO0,R.arb(0))
        self.assertTrue(contains(square.contain_gap(),0))
        self.assertTrue(contains(square.separators(ia.C0,R.arb(0))['CE'],0))
        self.assertTrue(contains(ia.label(ia.RHO0,R.arb(0)),0))


if __name__=='__main__':
    unittest.main(verbosity=2)
