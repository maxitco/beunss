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
    
    public boolean isEmptyField(Field field) {
        Field copy = field.copy();
        //check fields below
        while(this.walkField(copy,0,0,-1)) {
            if(!this.fieldMap.containsKey(copy)) {
                return false;
            }
        }
        return (this.isField(field) && !this.fieldMap.containsKey(field));
    }
    
    public Field getEmptyField(int x, int y) {
        Field empty = new Field(x,y,0);
        if (this.isEmptyField(empty)) {
            return empty;
        }
        else {
            while (walkField(empty,0,0,1)) {
                if (this.isEmptyField(empty)) {
                    return empty;
                }
            }
        }
        return null;
    }
    
    public boolean setField(Field field, Mark m) {
        if (this.isEmptyField(field)) {
            this.fieldMap.put(field, m);
            return true;
        }
        return false;
    }
    
    public boolean walkField(Field field, int xoff, int yoff, int zoff) {
        Field nextfield = new Field(field.x + xoff,field.y + yoff, field.z + zoff);
        if (this.isField(nextfield)) {
            field = nextfield;
            return true;
        }
        return false;
    }
    
    public boolean setField(int x, int y, Mark m) {
        Field newfield = null;
        if ((newfield = this.getEmptyField(x,y)) != null) {
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
}
