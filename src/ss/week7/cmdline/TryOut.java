package ss.week7.cmdline;

public class TryOut {
	public static void main(String[] args) {
		String a = "yolo|swagger";
		
		for(String input : a.split("\\|")) {
			System.out.println(input);	
		}
		
		
	}
}
