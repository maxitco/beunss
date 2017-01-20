package ss.week7.account;

import java.util.concurrent.locks.*;

public class Account {
	protected double balance = 0.0;

	//private final ReentrantLock lock = new ReentrantLock();
	//private final Condition write = lock.newCondition();
	
	public synchronized void transaction(double amount) {	
		while (balance + amount < -1000) { 
			try { 
				wait(); 
		   	} catch (InterruptedException e) { 
		   		 
		   	} 
		} 
		
			  balance = balance + amount; 
			  System.out.println(this.getBalance());
			  notifyAll(); 
	} 	
	
	public double getBalance() {
		return balance;
	}
}
