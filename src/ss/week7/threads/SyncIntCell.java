package ss.week7.threads;

/**
 * Correct communication between IntProducer en IntConsumer.
 */
public class SyncIntCell implements IntCell {
	private int value = 0;
	private boolean set = false;

	public synchronized void setValue(int valueArg) {
		while(set) {
			try { 
				wait();
			} catch(InterruptedException e1) {				
			}
		}
		this.value = valueArg;
		set = true;
		notifyAll();
	}

	public synchronized int getValue() {
		while(!set) {
			try { 
				wait();
			} catch(InterruptedException e1) {				
			}
		}
		set = false;
		notifyAll();
		return value;
	}
}
