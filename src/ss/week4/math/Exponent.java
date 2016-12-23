package ss.week4.math;

public class Exponent implements Function,Integrandable{
private Integer exp;

    //@ requires exponent != null;
    public Exponent(int exponent)
    {
        this.exp = new Integer(exponent);
    }
    //@pure;
    public double apply(double val) {
        return Math.pow(val, this.exp.doubleValue());
    }
    //@pure;
    public Function derivative() {
        return new LinearProduct(
                new Constant(this.exp.intValue()),
                new Exponent(this.exp.intValue() -1)
                );
    }
    //@pure;
    public String toString() {
        return "x^" + this.exp.toString();
    }
    
    public Function integrand() {
        return new LinearProduct(new Constant(1/(this.exp +1)),new Exponent(this.exp+1));
    }
}
