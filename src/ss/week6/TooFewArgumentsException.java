package ss.week6;

public class TooFewArgumentsException extends WrongArgumentException {
    public String getMessage() {
        return "Too few arguments, enter 2 strings";
    }
}
