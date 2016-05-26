import React from 'react'
import RToShowList from '../containers/RToShowList'
import RAddToShow from '../containers/RAddToShow'

const ToShowBlock = () => (
  <div>
    <h2>To Show</h2>
    <RToShowList />
    <RAddToShow />
  </div>
)

export default ToShowBlock

