package ss.week7.threads;
import java.util.concurrent.locks.*;

public class FineGrainedIntCell implements IntCell {
	private int value;
	private boolean set;
	
	private final Lock lock = new ReentrantLock();
	private final Condition write = lock.newCondition();
	private final Condition read = lock.newCondition();
	
	public void setValue(int valueArg) {
		lock.lock();
		while(set) {
			try { 
				write.await();
			} catch(InterruptedException e1) {				
			}
		}
		
		this.value = valueArg;
		set = true;
		read.signalAll();
		lock.unlock();
	}

	public int getValue() {
		lock.lock();
		while(!set) {
			try { 
				read.await();
			} catch(InterruptedException e1) {				
			}
		}
		set = false;
		write.signalAll();	
		lock.unlock();
		return value;		
	}
}
