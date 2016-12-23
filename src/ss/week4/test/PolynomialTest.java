package ss.week4.test;

import org.junit.Before;
import org.junit.Test;
import ss.week4.math.Exponent;
import ss.week4.math.Polynomial;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class PolynomialTest {

    private static final double DELTA = 1e-15;
    private static final double CONSTANT_VALUE = Math.PI;
    private double[] input = new double[4];
    private Polynomial poly;

    @Before
    public void setUp() {
        for (int i = 0;i<input.length; i++){
            input[i] = 1;
        }
        poly = new Polynomial(input);
        System.out.println(poly.toString());
        System.out.println(poly.derivative().toString());
        System.out.println(poly.integrand().toString());
    }

    @Test
    public void testApply() {
        assertEquals(1, poly.apply(0), DELTA);
        assertEquals(0, poly.apply(-1), DELTA);
        assertEquals(this.input.length, poly.apply(1), DELTA);
    }

    @Test
    public void testDerivative() {
        assertTrue(poly.derivative() instanceof Polynomial);
        assertEquals(6, poly.derivative().apply(1), DELTA);
    }
    
    @Test
    public void testIntegrand() {
        assertTrue(poly.integrand() instanceof Polynomial);
        assertEquals(((double)32/(double)3),poly.integrand().apply(2),DELTA);
    }
}
