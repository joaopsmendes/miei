package com.andreubita.poo.ficha3;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

public class Order {
    private String name;
    private int nif;
    private String address;
    private int orderId;
    private LocalDateTime orderTime;

    // Dependency over Ex7
    private List<OrderLine> orderLineList;

    public Order(){
        this.name = "André";
        this.nif = 777;
        this.address = "Portugal";
        this.orderId = 1;
        this.orderTime = LocalDateTime.now();
        this.orderLineList = new ArrayList<>(10);
    }

    public Order(String name, int nif, String address, int orderId,
                 LocalDateTime orderTime, List<OrderLine> orderLineList) {
        this.name = name;
        this.nif = nif;
        this.address = address;
        this.orderId = orderId;
        this.orderTime = orderTime;
        setOrderLineList(orderLineList);
    }

    public Order(Order order){
        setName(order.getName());
        setNif(order.getNif());
        setAddress(order.getAddress());
        setOrderId(order.getOrderId());
        setOrderTime(order.getOrderTime());
        setOrderLineList(order.getOrderLineList());
    }

    public double calcTotalValue(){
        return getOrderLineList().stream().mapToDouble(OrderLine::calcValueInLine).sum();
//        int total = 0;
//        for(OrderLine orderLine : getOrderLineList())
//            total += orderLine.calcValueInLine();
//        return total;
    }

    public double calcTotalRebate(){
        return getOrderLineList().stream().mapToDouble(OrderLine::getRebateValue).sum();
    }

    public double calcTotalQnt(){
        return getOrderLineList().stream().mapToDouble(OrderLine::getQnt).sum();
    }

    public boolean containsProduct(String ref){
        for(OrderLine orderLine : getOrderLineList())
            if(orderLine.getRef().equals(ref)) return true;
        return false;
    }

    public void addOrderLine(OrderLine orderLine){
        List<OrderLine> orderLines = new ArrayList<>(getOrderLineList());
        orderLines.add(orderLine.clone());
        this.orderLineList = orderLines;
    }

    public void remOrderLine(OrderLine orderLine){
        List<OrderLine> orderLines = new ArrayList<>(getOrderLineList());
        orderLines.remove(orderLine);
        this.orderLineList = orderLines;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public int getNif() {
        return nif;
    }

    public void setNif(int nif) {
        this.nif = nif;
    }

    public String getAddress() {
        return address;
    }

    public void setAddress(String address) {
        this.address = address;
    }

    public int getOrderId() {
        return orderId;
    }

    public void setOrderId(int orderId) {
        this.orderId = orderId;
    }

    public LocalDateTime getOrderTime() {
        return orderTime;
    }

    public void setOrderTime(LocalDateTime orderTime) {
        this.orderTime = orderTime;
    }

    public List<OrderLine> getOrderLineList() {
        List<OrderLine> newArr = new ArrayList<>();
        for(OrderLine crt : this.orderLineList)
            newArr.add(crt.clone());
        return newArr;
    }

    public void setOrderLineList(List<OrderLine> orderLineList) {
        List<OrderLine> newArr = new ArrayList<>();
        for(OrderLine crt : orderLineList)
            newArr.add(crt.clone());
        this.orderLineList = newArr;
    }

    @Override
    public Order clone(){
        return new Order(this);
    }

    @Override
    public String toString() {
        return "Order{" +
                "name='" + name + '\'' +
                ", nif=" + nif +
                ", address='" + address + '\'' +
                ", orderId=" + orderId +
                ", orderTime=" + orderTime +
                ", orderLineList=" + orderLineList +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Order order = (Order) o;
        return getNif() == order.getNif() &&
                getOrderId() == order.getOrderId() &&
                Objects.equals(getName(), order.getName()) &&
                Objects.equals(getAddress(), order.getAddress()) &&
                Objects.equals(getOrderTime(), order.getOrderTime()) &&
                Objects.equals(getOrderLineList(), order.getOrderLineList());
    }

    @Override
    public int hashCode() {
        return Objects.hash(getName(), getNif(), getAddress(), getOrderId(), getOrderTime(), getOrderLineList());
    }
}
