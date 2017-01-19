package ss.week7.account;

import java.lang.Thread;

public class MyThread implements Runnable{
	private double theAmount;
	private int theFrequency;
	private Account theAccount;
	
	public MyThread(double amount, int frequency, Account account) {
		assert(account != null);		
		this.theAmount = amount;
		this.theFrequency = frequency;
		this.theAccount = account;		
	}
	
	public void run() {
		
		for(int i = 0; i < theFrequency; i++) {
			theAccount.transaction(theAmount);
		}
	}
}
