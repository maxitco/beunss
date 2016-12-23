package ss.week4.math;

public class Constant implements Function, Integrandable{
    private double value;
    
    //@ requires input != null;
    public Constant(double input)
    {
        this.value = input;
    }
    //@pure;
    public double apply(double val) {
        return this.value;
    }
    //@pure;
    public Function derivative() {
        return new Constant(0);
    }
    //@pure;
    public String toString() {
        return Double.toString(this.value);
    }
    
    public Function integrand() {
        return new LinearProduct(new Exponent(1),this);
    }
    
}
