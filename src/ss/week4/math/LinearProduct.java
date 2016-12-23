package ss.week4.math;

public class LinearProduct extends Product implements Function,Integrandable{
    private Function f,c;
    public LinearProduct(Function in1,Function in2) {
        super(in1,in2);
        if (in1 instanceof Constant) {
            c = in1;
            f = in2;
        }
        else {
            c = in2;
            f = in1;
        }
    }

    public Function derivative() {

        return new LinearProduct(this.f.derivative(),this.c);

    }
    
    public Function integrand() {
        return new LinearProduct(this.c,((Integrandable)this.f).integrand());
    }
}
