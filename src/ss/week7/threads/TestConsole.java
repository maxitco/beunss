package ss.week7.threads;

public class TestConsole extends Thread{
	public TestConsole() {
		super();
	}
	
	public TestConsole(String input) {
		super(input);
	}
	
	public void run() {
		sum();
	}
	
	private void sum() {
		Integer firstInt = Console.readInt(this.getName() + ": get number 1?:");
		Integer secondInt = Console.readInt(this.getName() + ": get number 2?:");
		Integer sum = firstInt + secondInt;
		Console.println(this.getName() + ": " + firstInt.toString() + " + " + secondInt.toString() + " = " + sum.toString());
	}
	
	public static void main(String[] args) {
		new TestConsole("Thread A").start();
		new TestConsole("Thread B").start();
	}
	
}
