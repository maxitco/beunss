package ss.project;

import java.util.HashMap;
import java.util.Map;

public class Board {
    public static int MAXFIELD = 3;
    private Map<Field, Mark> fieldMap = new HashMap<Field, Mark>();
    
    public Board() {
        this.reset();
    }
    //@ensures (field.x <= MAXFIELD
    //@pure;
    public boolean isField(Field field) {
        return field.x <= MAXFIELD || field.y <= MAXFIELD || field.z <= MAXFIELD;
    }
    
    public boolean isEmpty(Field field) {
        return !this.fieldMap.containsKey(field);
    }
    
    public boolean setField(Field field, Mark m) {
        if (this.isField(field) && this.isEmpty(field)) {
            this.fieldMap.put(field, m);
            return true;
        }
        return false;
    }
    
    public Mark getMark(Field field) {
        return this.fieldMap.get(field);
    }
    
    public Field getFieldByCoordinate(int x,int y, int z) {
        Field result = new Field(x,y,z);
        if (this.isField(result)) {
            return result;
        }
        return null;
    }
    
    public int getNextZ(int x, int y) {
        Field tester = new Field(x,y,0);
        for (tester.z = 0; tester.z <= MAXFIELD; tester.z++) {
            if (this.isEmpty(tester)) {
                return tester.z;
            }
        }
    }
    
    
    public void reset() {
        this.fieldMap.clear();
    }
}
