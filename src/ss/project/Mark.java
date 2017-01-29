package ss.project;

public enum Mark {
    Black,White;
    
    public Mark other() {
        if (this == Black) {
            return White;
        } else {
            return Black;
        }
    }
}
