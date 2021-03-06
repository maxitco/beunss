package ss.project.game;

public class Field {
    public int x, y, z;

    public Field(int newx, int newy, int newz) {
        this.x = newx;
        this.y = newy;
        this.z = newz;
    }
    
    @Override
    public boolean equals(Object o) {
        if (o instanceof Field) {
            return this.hashCode() == ((Field) o).hashCode();
        }
        return false;
    }
    @Override
    public int hashCode() {
        return x * 100 + y * 10 + z;
    }
    
    public Field copy() {
        return new Field(this.x, this.y, this.z);
    }
    
    public String getMove() {
    	return this.x + " " + this.y;
    }
    
    public String toString() {
    	return "(" + this.x + "," + this.y + "," + this.z + ")";
    }
}
