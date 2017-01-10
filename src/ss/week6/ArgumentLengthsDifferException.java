package ss.week6;

public class ArgumentLengthsDifferException extends WrongArgumentException {
    int length1,length2;
    
    public ArgumentLengthsDifferException(int inputLength1, int inputLength2) {
        this.length1 = inputLength1;
        this.length2 = inputLength2;
    }
    
    public String getMessage() {
        return "The length of the input Strings is different\n"
        +"The first string has " + this.length1 + " characters.\n" 
        +"The second string 2 has " + this.length2 + " characters.";
    }  
}
