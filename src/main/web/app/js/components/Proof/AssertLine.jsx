import React from 'react'

const AssertLine = ({
  fields: { formula },
  onSubmit,
  error,
  resetForm,
  handleSubmit,
  submitting,
  onCloseClick
}) => {

  return (
    <form className="form-horizontal" onSubmit={ handleSubmit }>
      <div className="form-group bottom-no-margin">
        <div className="col-sm-6">
          <input type="text" {...formula}
           className="form-control monospace-font" placeholder="..." />
        </div>
        <div className="col-sm-3">
          <button className="btn btn-primary full-width">Justification</button>
        </div>
        <div className="col-sm-2 text-right">
          <button type="submit" className="btn btn-primary full-width"
           disabled={ submitting }>Add</button>
        </div>
        <div className="col-sm-1 text-right">
          <button type="button" className="btn btn-default full-width"
           onClick={ onCloseClick }>
            x
          </button>
        </div>
      </div>
    </form>
  )
}

export default AssertLine

