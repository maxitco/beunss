package ss.project.game;

import java.util.HashMap;
import java.util.Map;
import java.util.Observable;

public class Board extends Observable {
	public final static int MAXFIELD = 3;
	private Map<Field, Mark> fieldMap = new HashMap<Field, Mark>();

	public Board() {
		this.reset();		
	}
	/**
	 * Create a copy of the current board.
	 * @return New instance of board with all fields copied
	 */
	public Board copy() {
		Board copy = new Board();
		for (int x = 0; x <= MAXFIELD; x++) {
			for (int y = 0; y <= MAXFIELD; y++) {
				for (int z = 0; z <= MAXFIELD; z++) {
					Field field = new Field(x, y, z);
					if (!this.isEmptyField(field)) {
						copy.fieldMap.put(field, this.getMark(field));
					}
				}
			}
		}
		return copy;
	}
	
	/**
	 * @param field
	 * @return true if Field lies within the board boundaries.
	 */
	//@pure;
	public boolean isField(Field field) {
		return field.x >= 0 && field.x <= MAXFIELD &&
				field.y >= 0 && field.y <= MAXFIELD &&
				field.z >= 0 && field.z <= MAXFIELD;
	}
	
	/**
	 * @param field
	 * @return true if stack below empty field is filled.
	 */
	//@requires field != null && this.isEmptyField(field);
	//@pure;
	public boolean isReachableEmptyField(Field field) {
		Field copy = field.copy();
		//check fields below
		while ((copy = this.walkField(copy, 0, 0, -1)) != null) {
			if (!this.fieldMap.containsKey(copy)) {
				return false;
			}
		}
		return this.isField(field) && !this.fieldMap.containsKey(field);
	}
	
	/**
	 * @param field
	 * @return true if Field is not in fieldMap.
	 */
	//@requires field != null && this.isField(field);
	//@pure;
	public boolean isEmptyField(Field field) {
		return !this.fieldMap.containsKey(field);
	}

	/**
	 * @param x coordinate value
	 * @param y coordinate value
	 * @return empty Field based on x y coordinates and z stack hight.
	 */
	//@requires x >= 0 && x <= MAXFIELD;
	//@requires y >= 0 && y <= MAXFIELD;
	//@ensures (\result == null) || isReachableEmptyField(\result);
	//@pure;
	public Field getEmptyField(int x, int y) {
		Field empty = new Field(x, y, 0);
		if (this.isReachableEmptyField(empty)) {
			return empty;
		} else {
			while ((empty = walkField(empty, 0, 0, 1)) != null) {
				if (this.isReachableEmptyField(empty)) {
					return empty;
				}
			}
		}
		return null;
	}
	/**
	 * Registers Field with Mark in fieldMap and inform observer.
	 * @param field
	 * @param m
	 * @return true on success.
	 */
	//@requires isReachableEmptyField(field);
	//@ensures getMark(field) == m;
	public boolean setField(Field field, Mark m) {
		if (this.isReachableEmptyField(field)) {
			this.fieldMap.put(field, m);
			//use observer pattern to signal board change
			setChanged();
			notifyObservers("boardchanged");
			return true;			
		}
		return false;
	}
	/**
	 * Move a Field into any direction.
	 * @param field
	 * @param xoff
	 * @param yoff
	 * @param zoff
	 * @return Neighbor field
	 */
	//@requires field != null;
	//@requires field.x + xoff <= MAXFIELD && field.y + yoff <= MAXFIELD;
	//@requires field.z + zoff <= MAXFIELD;
	//@ensures \result == null || isField(\result);
	public Field walkField(Field field, int xoff, int yoff, int zoff) {
		Field nextfield = new Field(field.x + xoff, field.y + yoff, field.z + zoff);
		if (this.isField(nextfield)) {
			return nextfield;
		}
		return null;
	}
	/**
	 * Registers empty Field on coordinate with Mark in fieldMap.
	 * @param x
	 * @param y
	 * @param m
	 * @return true on success
	 */
	//@requires x > 0 && x <= MAXFIELD;
	//@requires y > 0 && y <= MAXFIELD;
	//@ensures getMark(getEmptyField(x, y)) == m;
	public boolean setField(int x, int y, Mark m) {
		Field newfield = this.getEmptyField(x, y);
		if (newfield != null) {
			return this.setField(newfield, m);
		}
		return false;
	}
	/**
	 * @param field
	 * @return Mark of given Field, or null if Field is empty.
	 */
	//@requires isField(field);
	//@pure;
	public Mark getMark(Field field) {
		if (this.isField(field)) {
			return this.fieldMap.get(field);
		}
		return null;
	}
	/**
	 * Empties the board.
	 */
	public void reset() {
		this.fieldMap.clear();
		setChanged();
        notifyObservers("boardchanged");
	}
	/**
	 * Checks a row for equal Marks along a direction.
	 * Starting Field must be along the boarder of the playing field.
	 * @param start
	 * @param xdir
	 * @param ydir
	 * @param zdir
	 * @param m
	 * @return true if complete row has same Mark
	 */
	/*@ requires (start.x == MAXFIELD || start.x == 0) ||
                 (start.y == MAXFIELD || start.y == 0) ||
                 (start.z == MAXFIELD || start.z == 0);
	 */
	//@pure;
	public boolean checkRow(Field start, int xdir, int ydir, int zdir, Mark m) {
		Field checker = start.copy();
		int count = 0;
		do {
			if (this.isEmptyField(checker) || !this.getMark(checker).equals(m)) {
				return false;
			}
			count++;
			checker = this.walkField(checker, xdir, ydir, zdir);
		} while (checker != null);
		if (count == MAXFIELD + 1) {
			return true;
		}
		return false;
	}
	/**
	 * Checks if there is a column filled with the same mark.
	 * @param m
	 * @return true if one of the columns has same Mark.
	 */
	//@pure;
	public boolean checkZcolums(Mark m) {
		for (int x = 0; x <= MAXFIELD; x++) {
			for (int y = 0; y <= MAXFIELD; y++) {
				Field zchecker = new Field(x, y, 0);
				if (this.checkRow(zchecker, 0, 0, 1, m)) {
					return true;
				}
			}
		}
		return false;
	}
	/**
	 * Checks all but the z-columns for winning rows of the same mark.
	 * @param m
	 * @return true if there is a complete row with same mark
	 */
	//@pure;
	public boolean checkPlanes(Mark m) {
		for (int i = 0; i <= MAXFIELD; i++) {
			//check all x-y planes
			for (int z = 0; z <= MAXFIELD; z++) {
				Field xchecker = new Field(0, i, z);
				Field ychecker = new Field(i, 0, z);
				if (this.checkRow(xchecker, 1, 0, 0, m) ||
						this.checkRow(ychecker, 0, 1, 0, m)) {
					return true;
				}
			}
			//check diagonal planes
			Field yzchecker = new Field(i, 0, 0); //startpoint x axis
			Field xzchecker = new Field(0, i, 0); //startpoint y axis
			Field yzdownchecker = new Field(i, MAXFIELD, 0); //opposite startpoint x axis
			Field xzdownchecker = new Field(MAXFIELD, i, 0); //opposite startpoint y axis
			//check cross-planes
			Field crosschecker = new Field(0, 0, i);
			Field crossdownchecker = new Field(0, MAXFIELD, i);
			if (
					this.checkRow(yzchecker, 0, 1, 1, m) ||
					this.checkRow(xzchecker, 1, 0, 1, m) ||
					this.checkRow(yzdownchecker, 0, -1, 1, m) ||
					this.checkRow(xzdownchecker, -1, 0, 1, m) ||
					this.checkRow(crosschecker, 1, 1, 0, m) ||
					this.checkRow(crossdownchecker, 1, -1, 0, m)
			) {
				return true;
			}
		}
		return false;
	}
	/**
	 * @param m
	 * @return true if any row is filled completely by Mark m.
	 */
	//@ensures checkPlanes(m) || checkZcolums(m);
	//@pure;
	public boolean isWinner(Mark m) {
		return this.checkPlanes(m) || this.checkZcolums(m);
	}
	/**
	 * @return mark of the winner, or null if there is no winner.
	 */
	//@ensures isWinner(\result) || \result == null;
	//@pure;
	public Mark getWinner() {
		Mark m = Mark.X;
		if (this.isWinner(m) && !this.isWinner(m.other())) {
			return m;
		} else if (this.isWinner(m.other())) {
			return m.other();
		} else {
			return null;
		}
	}
	/**
	 * @return true if the board has a winner or the board is full.
	 */
	//@pure;
	public boolean hasEnded() {
		if (this.isWinner(Mark.X) || this.isWinner(Mark.O) ||
				this.fieldMap.size() == MAXFIELD * MAXFIELD * MAXFIELD) {
			return true;
		}
		return false;
	}
	/**
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		String result = "";
		for (int y = MAXFIELD; y >= 0; y--) {
			for (int z = 0; z <= MAXFIELD; z++) {
				result = result + y;
				for (int x = 0; x <= MAXFIELD; x++) {
					Field out = new Field(x, y, z);
					if (this.isEmptyField(out)) {
						result = result + "[ ]";
					} else {
						result = result + "[" + this.getMark(out).toString() + "]";
					}
				}
				result = result + "   ";
			}
			result = result + "\n";
		}
		return result;
	}

}
