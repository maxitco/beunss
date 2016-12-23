package ss.week4.math;

public class Sum implements Function, Integrandable{
    private Function f1,f2;
    
    //@ requires in1 != null && in2 != null;
    Sum(Function in1,Function in2) {
        this.f1 = in1;
        this.f2 = in2;
    }
    
    public double apply(double input) {
        return this.f1.apply(input) + this.f2.apply(input);
    }
    
    public Function derivative() {
        return new Sum(this.f1.derivative(),this.f2.derivative());
    }
    
    public String toString() {
        return this.f1.toString() + " + " + this.f2.toString();
    }
    
    public Function integrand() {
        return new Sum(((Integrandable)this.f1).integrand(),((Integrandable)this.f2).integrand());
    }
}
