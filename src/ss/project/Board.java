package ss.project;

import java.util.HashMap;
import java.util.Map;

public class Board {
    public static int MAXFIELD = 3;
    private Map<Field, Mark> fieldMap = new HashMap<Field, Mark>();
    
    public Board() {
        this.reset();
    }
    
    //@pure;
    public boolean isField(Field field) {
        return field.x >= 0 && field.x <= MAXFIELD &&
               field.y >= 0 && field.y <= MAXFIELD &&
               field.z >= 0 && field.z <= MAXFIELD;
    }
    
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
    
    public boolean isEmptyField(Field field) {
        return !this.fieldMap.containsKey(field);
    }
    
    public Field getEmptyField(int x, int y) {
        Field empty = new Field(x, y, 0);
        if (this.isReachableEmptyField(empty)) {
            return empty;
        }
        else {
            while ((empty = walkField(empty, 0, 0, 1)) != null) {
                if (this.isReachableEmptyField(empty)) {
                    return empty;
                }
            }
        }
        return null;
    }
    
    public boolean setField(Field field, Mark m) {
        if (this.isReachableEmptyField(field)) {
            this.fieldMap.put(field, m);
            return true;
        }
        return false;
    }
    
    public Field walkField(Field field, int xoff, int yoff, int zoff) {
        Field nextfield = new Field(field.x + xoff, field.y + yoff, field.z + zoff);
        if (this.isField(nextfield)) {
            return nextfield;
        }
        return null;
    }
    
    public boolean setField(int x, int y, Mark m) {
        Field newfield = this.getEmptyField(x, y);
        if (newfield != null) {
            return this.setField(newfield, m);
        }
        return false;
    }
    
    public Mark getMark(Field field) {
        if (this.isField(field)) {
            return this.fieldMap.get(field);
        }
        return null;
    }
        
    public void reset() {
        this.fieldMap.clear();
    }
    /*@ requires (start.x == MAXFIELD || start.x == 0) ||
                 (start.y == MAXFIELD || start.y == 0) ||
                 (start.z == MAXFIELD || start.z == 0);
     */
    //@pure;
    public boolean checkRow(Field start, int xdir, int ydir, int zdir, Mark m) {
        Field checker = start.copy();
        for (int i = 0; i < MAXFIELD; i++) {
            if (this.isEmptyField(checker)) {
                return false;
            }
            if (!this.getMark(checker).equals(m)) {
                return false;
            }
            checker = this.walkField(checker, xdir, ydir, zdir);
            if (checker == null) {
                return false;
            }
        }
        return true;
    }
    
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
    
    public boolean isWinner(Mark m) {
        return this.checkPlanes(m) || this.checkZcolums(m);
    }
    
    public boolean hasWinner() {
        if (this.isWinner(Mark.Black) ^ this.isWinner(Mark.White)) {
            return true;
        }
        return false;
    }
    
    public String toString() {
        String result = "";
        for (int y = 0; y <= MAXFIELD; y++) {
            for (int z = 0; z <= MAXFIELD; z++) {
                for (int x = 0; x <= MAXFIELD; x++) {
                    Field out = new Field(x, y, z);
                    if (this.isEmptyField(out)) {
                        result = result + "[ ]";
                    }
                    else {
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
