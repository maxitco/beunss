package ss.week7.account;

public class AccountSync {
	
	private static int times = 10;
	
	
	public static void main(String[] args) {
		for(int i = 0; i<10; i++) {
			Account account1 = new Account(); 
			Thread thread1 = new Thread(new MyThread(-1000, times, account1));	
			Thread thread2 = new Thread(new MyThread(100, times, account1));
			
			thread1.start();
			thread2.start();
			
			
			try { 
			   thread1.join(); 
			   thread2.join(); 
			} catch (InterruptedException e) {} 
			//System.out.println(account1.getBalance()); 
			 
			/*
			if(account1.getBalance() < 0 || account1.getBalance() > 0) {
				
			} */
		}
	}
}
