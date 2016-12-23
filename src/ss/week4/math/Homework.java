package ss.week4.math;

public class Homework {

    public static void main(String[] args) {
        LinearProduct f1 = new LinearProduct(new Constant(3),new Exponent(5));
        double[] input = {3,7,3,9,43,6,2};
        Polynomial f2 = new Polynomial(input);
        Function f11 = f1.derivative();
        Function f12 = f1.integrand();
        Function f21 = f2.derivative();
        Function f22 = f2.integrand();
        
        System.out.println("f(x) = " + f1 + ",f(8) = " + f1.apply(8));
        System.out.println("f(x) = " + f11 + ",f(8) = " + f11.apply(8));
        System.out.println("f(x) = " + f12 + ",f(8) = " + f12.apply(8));
        
        System.out.println("f(x) = " + f2 + ",f(8) = " + f2.apply(8));
        System.out.println("f(x) = " + f21 + ",f(8) = " + f21.apply(8));
        System.out.println("f(x) = " + f22 + ",f(8) = " + f22.apply(8));
        

    }

}
