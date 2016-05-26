import React from 'react'

const AppRow = (props) => (
  <div className={["row", props.rowClass].join(' ')}>
    <div className="col-md-2"></div>
    <div className="col-md-8">
      { props.children }
    </div>
    <div className="col-md-2"></div>
  </div>

)

export default AppRow

