package ss.week6;

import java.util.Scanner;

public class Hello {
    public static void main(String[] args) {
            
            Scanner input = new Scanner(System.in);
            String name = "notempty";
            while (!name.isEmpty()) {
                System.out.println("Hello, what is your name?");
                name = input.nextLine();
                System.out.println("Hello " + name);
            }
            input.close();
        }
}
