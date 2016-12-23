package ss.week4.math;

public class Polynomial implements Function{
    double[] term;
    
    public Polynomial(double[] input) {
        this.term = new double[input.length];
        System.arraycopy(input, 0, this.term, 0, input.length);
    }
    
    public double apply(double value) {
        double result = 0;
        for (int i=0;i<this.term.length;i++) {
            result += this.term[i] * Math.pow(value, (double)i);
        }
        return result;
    }
    
    public Function derivative() {
        double[] result = new double[this.term.length -1];
        for (int i = 0;i<this.term.length -1;i++) {
            result[i] = this.term[i+1] * ((double)i+1);
        }
        return new Polynomial(result);
    }
    
    public String toString() {
        String result = Double.toString(this.term[0]);
        for (int i = 1;i<this.term.length;i++) {
            //System.out.println(" + " + Double.toString(this.term[i]) + "* x ^" + i);
            result = result + " + " + Double.toString(this.term[i]) + "*x^" + i;
        }
        return result;
    }
    
    public Function integrand() {
        double[] result = new double[this.term.length + 1];
        result[0] = 0;
        for (int i = 0;i<this.term.length;i++) {
            result[i+1] = this.term[i] / (i + 1);
        }
        return new Polynomial(result);
    }
}
