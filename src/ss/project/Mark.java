package ss.project;

public enum Mark {
    Black,White;
    
    public Mark other() {
        if (this == Black) {
            return White;
        }
        if (this == White) {
            return Black;
        }
        return null;
    }
    
    public String toString() {
        if (this == Black) {
            return new String("X");
        }
        if (this == White) {
            return new String("O");
        }
        return "";
    }
}
