package ss.week6;

public class Zipper {
    /*@
       requires s1 != null & s2 != null;
       requires s1.length() == s2.length();
     */
    public static String zip(String s1, String s2) {
        String result = "";
        for (int i = 0; i < s1.length(); i++) {
            result += Character.toString(s1.charAt(i))
                      + Character.toString(s2.charAt(i));
        }
        
        return result;
    }    

    public static void main(String[] args) throws TooFewArgumentsException, ArgumentLengthsDifferException {
        System.out.println(zip2(args[0], args[1]));
    }
    
    public static String zip2(String s1, String s2) throws TooFewArgumentsException, ArgumentLengthsDifferException {
        if (s1 == null || s2 == null) {
            throw new TooFewArgumentsException();            
        } else if (s1.length() != s2.length()) {
            throw new ArgumentLengthsDifferException(s1.length(), s2.length());
        } else {
            return zip(s1, s2);
        }
    }
}
