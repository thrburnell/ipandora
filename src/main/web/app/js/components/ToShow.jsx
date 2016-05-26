import React from 'react'

const ToShow = ({ active = false }) => {

  if (!active) {
    return null
  }

  return (
    <div className="panel panel-default">
      <div className="panel-heading">
        <h3 className="panel-title">To Show</h3>
      </div>
      <div className="panel-body">
        <form>
          <div className="form-group bottom-no-margin">
            <input type="text" className="form-control" placeholder="\\FORALL n in Nat. ..." />
          </div>
        </form>
      </div>
    </div>
  )
}

export default ToShow

