package ss.week7.threads;

import java.util.concurrent.locks.*;

public class TestSyncConsole extends Thread{
	private Lock lock = new ReentrantLock();
	
	public TestSyncConsole() {
		super();
	}
	
	public TestSyncConsole(String input) {
		super(input);
	}
	
	public void run() {
		lock.lock();
		try {
			sum();
		} finally {
			lock.unlock();
		}
	}
	
	private synchronized void sum() {		
			int firstInt = SyncConsole.readInt(this.getName() + ": get number 1?:");
			int secondInt = SyncConsole.readInt(this.getName() + ": get number 2?:");	
			SyncConsole.println(this.getName() + ": " + firstInt + " + " + secondInt + " = " + (firstInt + secondInt));
		
	}
	/*
	private synchronized void sum() {
		
		 int firstInt = SyncConsole.readInt(this.getName() + ": get number 1?:");
		 int secondInt = SyncConsole.readInt(this.getName() + ": get number 2?:");	
		 SyncConsole.println(this.getName() + ": " + firstInt + " + " + secondInt + " = " + (firstInt + secondInt));
		
		
	} 	
	*/
	
	public static void main(String[] args) {
		new TestSyncConsole("Thread A").start();
		new TestSyncConsole("Thread B").start();
	}
	
}
