package ss.project;

public class ClientHandler {
    public static int getPort(String input, String USAGE) {
    	int result = 0;
    	try {
    		result = Integer.parseInt(input);
        } catch (NumberFormatException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: " + input
            		           + " is not an integer");
            System.exit(0);
        }
    	return result;
    }
}
 